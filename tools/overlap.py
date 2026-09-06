"""How much model latency the second worker actually overlapped, per run.

One worker issues one step call at a time, so two calls in flight is two
workers. The exception is the plan pair, which one turn fires together, so
two concurrent plan calls are not counted.

    python tools/overlap.py outputs/board
"""
from __future__ import annotations

import datetime
import json
import pathlib
import statistics
import sys


def moment(stamp: str) -> float:
    return datetime.datetime.fromisoformat(stamp.replace("Z", "+00:00")).timestamp()


def kind(request: dict) -> str:
    for message in request.get("messages", []):
        if message.get("role") == "system":
            head = message["content"]
            if head.startswith("You extend"):
                return "step"
            if head.startswith("You audit"):
                return "audit"
            if head.startswith("You are a competition"):
                return "plan"
    return "other"


def calls(events: pathlib.Path) -> tuple[list[tuple[float, float, str]], float]:
    open_at, spans, wall = {}, [], 0.0
    for line in events.read_text().splitlines():
        event = json.loads(line)
        if event.get("event") == "llm_request":
            open_at[event["call_id"]] = (moment(event["timestamp"]), kind(event["request"]))
        elif event.get("event") == "llm_response":
            began = open_at.pop(event["call_id"], None)
            if began is not None:
                spans.append((began[0], moment(event["timestamp"]), began[1]))
        elif event.get("event") == "problem_finished":
            wall = event.get("wall_s", 0.0)
    return spans, wall


def overlapped(spans: list[tuple[float, float, str]]) -> tuple[float, float]:
    """(seconds with any call in flight, seconds two workers were both waiting)"""
    edges = sorted({t for begin, end, _ in spans for t in (begin, end)})
    busy = second = 0.0
    for lo, hi in zip(edges, edges[1:]):
        live = [k for begin, end, k in spans if begin <= lo and hi <= end]
        if not live:
            continue
        busy += hi - lo
        if len(live) >= 2 and not (len(live) == 2 and all(k == "plan" for k in live)):
            second += hi - lo
    return busy, second


def main() -> int:
    root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "outputs/board")
    rows, agent_walls = [], []
    for events in sorted(root.rglob("events.jsonl")):
        spans, wall = calls(events)
        # docs/ARCHITECTURE.md times the agent, not the harness: the comparator
        # is excluded, so the summary below must read the agent's own wall.
        result = events.parent / "result.json"
        if result.exists():
            meta = json.loads(result.read_text()).get("agent_metadata") or {}
            agent_walls.append(meta.get("wall_s", wall))
        if not spans:
            continue
        busy, second = overlapped(spans)
        rows.append((events.parts[-3], len(spans), busy, second, wall))
    if not rows:
        print(f"no model calls recorded under {root}")
        return 0
    print(f"{'problem':22s} {'calls':>5s} {'model_s':>8s} {'overlapped_s':>12s} {'wall_s':>8s} {'share':>6s}")
    for name, n, busy, second, wall in rows:
        print(f"{name:22s} {n:5d} {busy:8.1f} {second:12.1f} {wall:8.1f} "
              f"{second / wall * 100 if wall else 0:5.1f}%")
    n = sum(r[1] for r in rows)
    busy, second, wall = (sum(r[i] for r in rows) for i in (2, 3, 4))
    print("-" * 66)
    print(f"{f'{len(rows)} runs with calls':22s} {n:5d} {busy:8.1f} {second:12.1f} {wall:8.1f} "
          f"{second / wall * 100:5.1f}%")
    print(f"\n{len(agent_walls)} runs, agent wall (comparator excluded): median "
          f"{statistics.median(agent_walls):.1f} s, {sum(1 for w in agent_walls if w < 60)} "
          f"under a minute, slowest {max(agent_walls):.1f} s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
