"""Outer concurrent problem scheduler and judging entrypoint."""

from __future__ import annotations

import argparse
import atexit
import json
import os
import platform
import re
import signal
import subprocess
import sys
import time
import uuid
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from .artifacts import atomic_write_json, atomic_write_text, aggregate_results, build_transcript
from .config import HarnessSettings
from .events import read_events
from .lean import cleanup_session_containers
from .manifest import ProblemSet, ProblemSpec, load_problem_set

try:
    from tqdm.auto import tqdm
except ImportError:  # pragma: no cover - dependency fallback for editable dev checkouts
    tqdm = None


@dataclass
class RunningWorker:
    spec: ProblemSpec
    process: subprocess.Popen
    started: float
    session_id: str
    out_dir: Path


_ACTIVE_WORKERS: list[RunningWorker] = []
_SRC_ROOT = Path(__file__).resolve().parents[1]

def _shutdown_active_workers() -> None:
    """Best-effort cleanup for interruption and ordinary interpreter exit."""

    for worker in list(_ACTIVE_WORKERS):
        if worker.process.poll() is None:
            try:
                worker.process.terminate()
                worker.process.wait(timeout=3)
            except (OSError, subprocess.TimeoutExpired):
                try:
                    worker.process.kill()
                    worker.process.wait(timeout=3)
                except (OSError, subprocess.TimeoutExpired):
                    pass
        cleanup_session_containers(worker.session_id)
    _ACTIVE_WORKERS.clear()


atexit.register(_shutdown_active_workers)


def _progress_bar(total: int):
    if tqdm is None:
        return None
    return tqdm(
        total=total,
        desc="problems",
        unit="problem",
        dynamic_ncols=True,
        disable=not sys.stderr.isatty(),
    )


def _update_progress(progress, status_counts: dict[str, int], outcome: str) -> None:
    if progress is None:
        return
    status_counts[outcome] = status_counts.get(outcome, 0) + 1
    progress.set_postfix(status_counts, refresh=False)
    progress.update(1)


def _slug(value: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9._-]+", "-", value.strip()).strip("-._").lower()
    return slug or "agent"


def _agent_name(agent: str) -> str:
    module_name, _separator, _attribute = agent.partition(":")
    if module_name == "baselines.simple_agent":
        return "baseline"
    if module_name == "submission.agent":
        return "submission"
    if module_name.startswith("baselines."):
        name = module_name.rsplit(".", 1)[-1]
        return _slug(name.removesuffix("_agent") or name)
    return _slug(module_name.rsplit(".", 1)[-1] if module_name else agent)


def _new_timestamp(agent_dir: Path) -> str:
    base = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
    timestamp = base
    suffix = 2
    while (agent_dir / timestamp).exists():
        timestamp = f"{base}-{suffix}"
        suffix += 1
    return timestamp


def _latest_run_path(agent_dir: Path) -> Path:
    candidates = sorted(
        (path.parent for path in agent_dir.rglob("run.json") if path.is_file()),
        key=lambda path: ((path / "run.json").stat().st_mtime, str(path)),
    )
    if not candidates:
        raise ValueError(f"no resumable runs found under {agent_dir}")
    return candidates[-1]


def resolve_output_dir(out_root: Path, *, agent: str, resume: str | None) -> tuple[Path, str, str, bool]:
    agent_name = _agent_name(agent)
    agent_dir = out_root / agent_name
    if resume is None:
        agent_dir.mkdir(parents=True, exist_ok=True)
        timestamp = _new_timestamp(agent_dir)
        return agent_dir / timestamp, agent_name, timestamp, False

    if resume == "latest":
        if not agent_dir.is_dir():
            raise ValueError(f"cannot resume latest; missing agent output directory: {agent_dir}")
        run_dir = _latest_run_path(agent_dir)
        run_name = str(run_dir.relative_to(agent_dir))
    else:
        relative = Path(resume)
        if relative.is_absolute() or any(part in {"", ".", ".."} for part in relative.parts):
            raise ValueError("--resume must be 'latest' or a safe path under the selected agent")
        run_dir = agent_dir / relative
        run_name = str(relative)
    if not run_dir.is_dir():
        raise ValueError(f"cannot resume missing run directory: {run_dir}")
    return run_dir, agent_name, run_name, True


def _worker_config(
    problem_set: ProblemSet,
    spec: ProblemSpec,
    out_dir: Path,
    settings: HarnessSettings,
    agent: str,
    session_id: str,
) -> dict[str, Any]:
    description_path, challenge_path = problem_set.paths(spec)
    return {
        "schema_version": 1,
        "problem_id": spec.id,
        "description": description_path.read_text(encoding="utf-8"),
        "challenge": challenge_path.read_text(encoding="utf-8"),
        "problem_metadata": spec.metadata,
        "theorem_names": list(spec.theorem_names),
        "definition_names": list(spec.definition_names),
        "numeric_answer_names": list(spec.numeric_answer_names),
        "out_dir": str(out_dir),
        "budget_usd": settings.budget_usd,
        "time_limit_s": settings.time_limit_s,
        "lean_image": settings.lean_image,
        "lean_check_timeout_s": settings.lean_check_timeout_s,
        "comparator_timeout_s": settings.comparator_timeout_s,
        "verify_reserve_s": settings.verify_reserve_s,
        "agent": agent,
        "session_id": session_id,
    }


def _recover_worker(worker: RunningWorker, problem_set: ProblemSet, *, status: str, message: str) -> None:
    events_path = worker.out_dir / "events.jsonl"
    solution_path = worker.out_dir / "solution.lean"
    if not solution_path.exists():
        _description, challenge_path = problem_set.paths(worker.spec)
        atomic_write_text(solution_path, challenge_path.read_text(encoding="utf-8"))
    events = read_events(events_path)
    actual = sum(
        float(event.get("actual_cost_usd") or 0.0)
        for event in events if event.get("event") == "llm_response"
    )
    models = sorted({
        event.get("request", {}).get("model") for event in events
        if event.get("event") == "llm_request" and event.get("request", {}).get("model")
    })
    result = {
        "schema_version": 1,
        "problem_id": worker.spec.id,
        "status": status,
        "passed": False,
        "points": 0,
        "comparator": {"passed": False, "output": {"error": message}},
        "answer_shape": {"passed": False, "errors": ["worker did not finish grading"]},
        "budget": {
            "limit_usd": None,
            "spent_usd": round(actual, 10),
            "reserved_usd": 0.0,
            "accounting_complete": False,
        },
        "within_time": status != "timed_out",
        "wall_s": round(time.monotonic() - worker.started, 3),
        "models_used": models,
        "both_required_models_used": False,
        "agent_error": {"type": status, "message": message},
        "agent_metadata": {},
    }
    atomic_write_json(worker.out_dir / "result.json", result)
    atomic_write_json(
        worker.out_dir / "transcript.json",
        build_transcript(events_path, problem_id=worker.spec.id),
    )


def run(
    *,
    problems_dir: Path,
    out_dir: Path,
    settings: HarnessSettings,
    agent: str,
    agent_name: str | None = None,
    timestamp: str | None = None,
    resume: bool = False,
) -> dict[str, Any]:
    agent_name = agent_name or _agent_name(agent)
    timestamp = timestamp or out_dir.name
    problem_set = load_problem_set(problems_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    if not resume:
        for root_artifact in ("run.json", "summary.json"):
            path = out_dir / root_artifact
            if path.exists() or path.is_symlink():
                if not path.is_file() and not path.is_symlink():
                    raise ValueError(f"output artifact path is not a file: {path}")
                path.unlink()
    run_id = uuid.uuid4().hex
    started_at = datetime.now(UTC)
    started_monotonic = time.monotonic()
    run_path = out_dir / "run.json"
    if resume and run_path.exists():
        try:
            run_meta = json.loads(run_path.read_text(encoding="utf-8"))
            if not isinstance(run_meta, dict):
                raise TypeError
        except (json.JSONDecodeError, TypeError):
            run_meta = {}
        run_id = str(run_meta.get("run_id") or run_id)
        run_meta.update({
            "schema_version": 1,
            "run_id": run_id,
            "set": problem_set.name,
            "agent": agent,
            "agent_name": agent_name,
            "timestamp": timestamp,
            "resumed_at": started_at.isoformat(),
            "n_workers": settings.n_workers,
            "budget_usd_per_problem": settings.budget_usd,
            "time_limit_s_per_problem": settings.time_limit_s,
            "lean_image": settings.lean_image,
            "api_key_configured": bool(settings.api_key),
            "python": sys.version.split()[0],
            "platform": platform.platform(),
        })
    else:
        run_meta = {
            "schema_version": 1,
            "run_id": run_id,
            "set": problem_set.name,
            "started_at": started_at.isoformat(),
            "agent": agent,
            "agent_name": agent_name,
            "timestamp": timestamp,
            "n_workers": settings.n_workers,
            "budget_usd_per_problem": settings.budget_usd,
            "time_limit_s_per_problem": settings.time_limit_s,
            "lean_image": settings.lean_image,
            "api_key_configured": bool(settings.api_key),
            "python": sys.version.split()[0],
            "platform": platform.platform(),
        }
    atomic_write_json(run_path, run_meta)

    pending = []
    skipped = 0
    for spec in problem_set.problems:
        result_path = out_dir / spec.id / "result.json"
        if resume and result_path.is_file():
            try:
                existing = json.loads(result_path.read_text(encoding="utf-8"))
                if existing.get("problem_id") == spec.id and isinstance(existing.get("status"), str):
                    skipped += 1
                    continue
            except json.JSONDecodeError:
                pass
        pending.append(spec)
    running: list[RunningWorker] = []
    global _ACTIVE_WORKERS
    _ACTIVE_WORKERS = running
    completed = 0
    status_counts: dict[str, int] = {}
    if skipped:
        status_counts["resumed"] = skipped
    progress = _progress_bar(len(pending))
    try:
        while pending or running:
            while pending and len(running) < settings.n_workers:
                spec = pending.pop(0)
                problem_out = out_dir / spec.id
                problem_out.mkdir(parents=True, exist_ok=True)
                for artifact in (
                    "solution.lean", "result.json", "transcript.json", "events.jsonl",
                    "checkpoint.json", "worker-config.json",
                ):
                    path = problem_out / artifact
                    if path.exists() or path.is_symlink():
                        if not path.is_file() and not path.is_symlink():
                            raise ValueError(f"output artifact path is not a file: {path}")
                        path.unlink()
                session_id = uuid.uuid4().hex
                config = _worker_config(problem_set, spec, problem_out, settings, agent, session_id)
                config_path = problem_out / "worker-config.json"
                atomic_write_json(config_path, config)
                worker_env = os.environ.copy()
                worker_env["PYTHONPATH"] = (
                    str(_SRC_ROOT) if not worker_env.get("PYTHONPATH")
                    else f"{_SRC_ROOT}{os.pathsep}{worker_env['PYTHONPATH']}"
                )
                process = subprocess.Popen(
                    [sys.executable, "-m", "re_harness.worker", "--config", str(config_path)],
                    env=worker_env,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                )
                running.append(RunningWorker(spec, process, time.monotonic(), session_id, problem_out))

            for worker in list(running):
                return_code = worker.process.poll()
                elapsed = time.monotonic() - worker.started
                if return_code is None and elapsed <= settings.time_limit_s:
                    continue
                if return_code is None:
                    worker.process.terminate()
                    try:
                        worker.process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        worker.process.kill()
                        worker.process.wait(timeout=5)
                    cleanup_session_containers(worker.session_id)
                    _recover_worker(
                        worker, problem_set, status="timed_out",
                        message=f"problem exceeded {settings.time_limit_s:.1f}s wall-clock limit",
                    )
                elif return_code != 0 and not (worker.out_dir / "result.json").exists():
                    cleanup_session_containers(worker.session_id)
                    _recover_worker(
                        worker, problem_set, status="harness_error",
                        message=f"worker exited with status {return_code}",
                    )
                running.remove(worker)
                completed += 1
                result_path = worker.out_dir / "result.json"
                outcome = "unknown"
                if result_path.exists():
                    try:
                        outcome = json.loads(result_path.read_text(encoding="utf-8")).get("status", "unknown")
                    except json.JSONDecodeError:
                        outcome = "invalid-result"
                _update_progress(progress, status_counts, outcome)
            if running:
                time.sleep(0.1)
    finally:
        if progress is not None:
            progress.close()

    summary = aggregate_results(
        out_dir, [spec.id for spec in problem_set.problems], set_name=problem_set.name
    )
    summary["run_id"] = run_id
    summary["wall_s"] = round(time.monotonic() - started_monotonic, 3)
    summary["finished_at"] = datetime.now(UTC).isoformat()
    atomic_write_json(out_dir / "summary.json", summary)
    run_meta = json.loads(run_path.read_text(encoding="utf-8"))
    run_meta.update({
        "finished_at": summary["finished_at"],
        "wall_s": summary["wall_s"],
        "resumed": resume,
        "resumed_skipped_problems": skipped,
        "executed_problems": completed,
    })
    atomic_write_json(out_dir / "run.json", run_meta)
    return summary


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run the take-home agent harness")
    parser.add_argument("--problems", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--n-workers", type=int, default=None)
    parser.add_argument(
        "--resume",
        default=None,
        help="resume an existing run for this agent by timestamp/path, or use 'latest'",
    )
    parser.add_argument(
        "--agent", default=os.environ.get("TAKEHOME_AGENT", "submission.agent:create_agent")
    )
    args = parser.parse_args(argv)
    if args.n_workers is not None and args.n_workers < 1:
        parser.error("--n-workers must be >= 1")
    settings = HarnessSettings.from_env(n_workers=args.n_workers)

    def interrupted(signum: int, _frame: Any) -> None:
        _shutdown_active_workers()
        raise SystemExit(128 + signum)

    previous_handlers = {
        signum: signal.signal(signum, interrupted)
        for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)
        if hasattr(signal, signal.Signals(signum).name)
    }
    try:
        out_dir, agent_name, timestamp, resume = resolve_output_dir(
            args.out, agent=args.agent, resume=args.resume
        )
        summary = run(
            problems_dir=args.problems,
            out_dir=out_dir,
            settings=settings,
            agent=args.agent,
            agent_name=agent_name,
            timestamp=timestamp,
            resume=resume,
        )
    finally:
        _shutdown_active_workers()
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)
    print(
        f"out {out_dir}; "
        f"score {summary['total_points']}/{summary['max_points']}; "
        f"actual spend ${summary['actual_cost_usd']:.6f}",
        flush=True,
    )
    return 0
