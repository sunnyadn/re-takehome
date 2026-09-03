"""Per-run accounting for the writeup: calls and spend per model from
transcript.json, steps, audits and Lean-only closes from result.json.
Usage: python tools/account.py outputs/board/*/"""
from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path


def short(model: str) -> str:
    return "Q" if "qwen" in model else ("G" if "gpt" in model else model)


def account(run_dir: Path) -> dict:
    result = next(run_dir.rglob("result.json"))
    transcript = result.with_name("transcript.json")
    d = json.loads(result.read_text())
    calls: Counter = Counter()
    spend: Counter = Counter()
    if transcript.exists():
        for c in json.loads(transcript.read_text()).get("calls", []):
            m = short(c["request"]["model"])
            calls[m] += 1
            spend[m] += c.get("actual_cost_usd") or 0.0
    events = (d.get("agent_metadata") or {}).get("events", [])
    steps: Counter = Counter()
    audits: Counter = Counter()
    lean_closes = 0
    for e in events:
        kind = e.get("kind") or e.get("stage")
        by = short(e.get("by") or "")
        if kind == "step":
            steps[(by, bool(e.get("accepted")))] += 1
        elif kind == "audit":
            audits[by] += 1
        elif kind in ("closers", "witnesses", "collapse") and e.get("accepted"):
            lean_closes += 1
    return {
        "problem": d.get("problem_id"),
        "passed": bool(d.get("passed")),
        "wall_s": round((d.get("agent_metadata") or {}).get("wall_s") or d.get("wall_s") or 0),
        "spend_usd": round(sum(spend.values()), 4),
        "calls": {m: calls[m] for m in sorted(calls)},
        "steps": {m: f"{steps[(m, True)]}/{steps[(m, True)] + steps[(m, False)]}"
                  for m in sorted({m for m, _ in steps})},
        "audits": dict(audits),
        "lean_closes": lean_closes,
        "events": len(events),
        "turns": (d.get("agent_metadata") or {}).get("turns"),
    }


if __name__ == "__main__":
    rows = [account(Path(p)) for p in sys.argv[1:]]
    for r in rows:
        print(json.dumps(r, ensure_ascii=False))
