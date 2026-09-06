"""Replay a recorded run through the agent loop, with no API calls and no Lean.

Prompts the change invents are reported as misses, never answered. Measured on
`outputs/board-2026-09-06/`: 14 of the 16 reach the recorded outcome with no
miss at all; p10_factorial_pow and rmo_2001_2 diverge with 4 misses each."""
from __future__ import annotations

import argparse
import asyncio
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src"))


def llm_key(model: str, messages: list[dict], max_tokens: int) -> str:
    body = json.dumps([model, messages, max_tokens], sort_keys=True)
    return hashlib.sha256(body.encode()).hexdigest()


def lean_key(source: str) -> str:
    return hashlib.sha256(source.encode()).hexdigest()


@dataclass
class Cache:
    llm: dict[str, list[dict]]
    lean: dict[str, list[dict]]
    order: list[str]

    @staticmethod
    def take(table: dict[str, list], key: str):
        """The next recorded answer for this key, last one repeating at the end.

        Sampling and Lean are both nondeterministic, so a key is not a value."""

        queue = table.get(key)
        if not queue:
            return None
        return queue.pop(0) if len(queue) > 1 else queue[0]

    @classmethod
    def from_events(cls, paths: list[Path]) -> "Cache":
        llm: dict[str, list[dict]] = {}
        lean: dict[str, list[dict]] = {}
        order: list[str] = []
        for path in paths:
            pending: dict[str, dict] = {}
            for raw in path.read_text().splitlines():
                try:
                    event = json.loads(raw)
                except ValueError:
                    continue
                kind = event.get("event")
                if kind == "llm_request":
                    pending[event["call_id"]] = event["request"]
                elif kind == "llm_response":
                    request = pending.pop(event.get("call_id"), None)
                    if request is None:
                        continue
                    key = llm_key(request["model"], request["messages"], request["max_tokens"])
                    llm.setdefault(key, []).append(event["response"])
                    order.append(key)
                elif kind == "lean_check":
                    lean.setdefault(event["source_sha256"], []).append(event["result"])
        return cls(llm=llm, lean=lean, order=order)


class ReplayExhausted(Exception):
    """The recording ran out, which a replay with no real clock always does."""


class ReplayLLM:
    def __init__(self, cache: Cache):
        self.cache, self.hits, self.misses = cache, 0, []

    async def complete(self, *, model, messages, max_tokens, **kwargs):
        key = llm_key(model, list(messages), max_tokens)
        found = self.cache.take(self.cache.llm, key)
        if found is None:
            self.misses.append((model, max_tokens, messages[-1]["content"][:80]))
            raise ReplayExhausted("no recorded answer for this prompt")
        self.hits += 1
        choice = found["choices"][0]
        message = choice.get("message") or {}
        return SimpleNamespace(
            content=message.get("content") or "",
            tool_calls=list(message.get("tool_calls") or []),
            finish_reason=choice.get("finish_reason"),
            usage=found["usage"],
        )


class ReplayLean:
    def __init__(self, cache: Cache):
        self.cache, self.hits, self.misses = cache, 0, 0

    async def check_file(self, source, **kwargs):
        found = self.cache.take(self.cache.lean, lean_key(source))
        if found is None:
            self.misses += 1
            # An unseen file cannot be judged, so it fails rather than guessing.
            return SimpleNamespace(accepted=False, messages=[], has_sorry=False,
                                   timed_out=False, duration_ms=0,
                                   container_restarted=False, replay_miss=True)
        self.hits += 1
        return SimpleNamespace(replay_miss=False, **found)


async def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("run_dir", help="a .../<timestamp>/<problem_id>/ directory")
    # A replay pays no Lean or API time, so the agent burns its whole budget
    # doing nothing and only the clock stops it. Measured on p03: with the
    # old unbounded default the loop never returned.
    ap.add_argument("--time-limit", type=float, default=60.0,
                    help="seconds of agent budget (default 60)")
    args = ap.parse_args()

    from re_harness import Problem
    from submission.board_agent import BoardAgent
    from submission.config import Config

    run = Path(args.run_dir)
    cache = Cache.from_events([run / "events.jsonl"])
    result = json.loads((run / "result.json").read_text())
    pid = result["problem_id"]
    problems = ROOT / "sample-problems" / pid
    problem = Problem(
        id=pid,
        description=(problems / "problem.md").read_text(),
        challenge=(problems / "challenge.lean").read_text(),
    )
    agent = BoardAgent(Config(time_limit_s=args.time_limit))
    llm, lean = ReplayLLM(cache), ReplayLean(cache)
    seen: list[tuple[str, dict]] = []
    services = SimpleNamespace(
        llm=llm, lean=lean,
        checkpoint=lambda source, meta=None: seen.append((source, meta or {})),
    )

    calls = sum(len(v) for v in cache.llm.values())
    checks = sum(len(v) for v in cache.lean.values())
    print(f"cache: {calls} llm answers over {len(cache.llm)} prompts, "
          f"{checks} lean verdicts over {len(cache.lean)} sources, from {pid}")
    try:
        out = await agent.solve(problem, services)
    except ReplayExhausted:
        out = None
    print(f"llm hits={llm.hits} misses={len(llm.misses)}   "
          f"lean hits={lean.hits} misses={lean.misses}")
    for m in llm.misses[:5]:
        print(f"  MISS {m[0]} max_tokens={m[1]} :: {m[2]!r}")
    if out is None:
        last = seen[-1][1] if seen else {}
        print(f"recording exhausted after {llm.hits} calls; "
              f"best checkpoint {last or None}")
    if out is not None:
        meta = out.metadata
        print(f"replayed outcome: accepted={meta.get('accepted_by_repl')} "
              f"solved_by={meta.get('solved_by')} spend=${meta.get('spend_usd')}")
        print(f"recorded outcome: passed={result['passed']} "
              f"spend=${result['budget']['spent_usd']:.4f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(asyncio.run(main()))
