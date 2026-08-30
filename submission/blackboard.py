"""An agent whose state is what has been proved, not the latest file.

Each accepted `have` is permanent, so a bad turn cannot lose earlier work.
Measured motivation: every line of a 3.9-hour run ended worse than its best."""

from __future__ import annotations

import re
import time
from dataclasses import dataclass, field
from typing import Any, Sequence

from re_harness import AgentResult, LLMCallError, Problem, Services

from submission.agent import (
    COCKTAIL, answer_names, banned_constructs, error_messages,
    extract_lean, normalise_imports, numeric_answers_are_literals,
    scoring_faults, statement_drift, wrap_tactic,
)

SORRY = re.compile(r"^(\s*)sorry\s*$")
ANSWER_SORRY = re.compile(r"^(\s*(?:abbrev|def)\s+\S+.*:=\s*)sorry\s*$")
STEP = re.compile(r"HAVE\s*:\s*(.+?)\s*:=\s*by\s+(.+)", re.I)
CLOSE = re.compile(r"CLOSE\s*:\s*(.+)", re.I)
ANSWER = re.compile(r"^\s*ANSWER\s*:\s*(\S+)\s*$", re.M)
HAVE_HEAD = re.compile(r"^\s*have\s+(.+?)\s*:=\s*by\s*(.*)$")
UNSOLVED = "unsolved goals"
STEP_TOKENS = 6000
# A turn that parses nothing is common, so one barren pass must not end the run.
STUCK_LIMIT = 12
TURN_RESERVE_S = 90.0


def _last(pattern: re.Pattern[str], text: str) -> re.Match[str] | None:
    """The final directive in a reply that reasoned before answering."""

    found = list(pattern.finditer(text))
    return found[-1] if found else None


@dataclass
class Slot:
    """One `sorry` in the challenge and everything proved for it so far."""

    line: int
    indent: str
    prefix: str = ""
    steps: list[tuple[str, str]] = field(default_factory=list)
    closer: str | None = None
    answer: str | None = None
    goal: str = ""
    tried: set[str] = field(default_factory=set)
    last: tuple[str, str] = ("", "")

    @property
    def is_answer(self) -> bool:
        return bool(self.prefix)

    @property
    def done(self) -> bool:
        return self.answer is not None if self.is_answer else self.closer is not None


def find_slots(challenge: str) -> list[Slot]:
    """Every `sorry` the challenge asks the agent to replace."""

    slots = []
    for i, line in enumerate(challenge.splitlines(), start=1):
        answer = ANSWER_SORRY.match(line)
        if answer:
            slots.append(Slot(line=i, indent="", prefix=answer.group(1)))
            continue
        plain = SORRY.match(line)
        if plain:
            slots.append(Slot(line=i, indent=plain.group(1) or "  "))
    return slots


def render(challenge: str, slots: Sequence[Slot]) -> tuple[str, dict[int, tuple[int, int]]]:
    """The file as the blackboard currently stands, and each slot's line range."""

    by_line = {s.line: s for s in slots}
    out: list[str] = []
    spans: dict[int, tuple[int, int]] = {}
    for i, line in enumerate(challenge.splitlines(), start=1):
        slot = by_line.get(i)
        if slot is None:
            out.append(line)
            continue
        start = len(out) + 1
        if slot.is_answer:
            out.append(f"{slot.prefix}{slot.answer if slot.answer is not None else 'sorry'}")
        else:
            for kind, tactic in slot.steps:
                out.append(f"{slot.indent}have {kind} := by {tactic}")
            out.append(f"{slot.indent}{slot.closer or 'sorry'}")
        spans[slot.line] = (start, len(out))
    return "\n".join(out) + "\n", spans


def error_lines(messages: Sequence[dict[str, Any]]) -> list[int]:
    """Line of every positioned error in the file as rendered."""

    out = []
    for m in messages:
        if m.get("severity") != "error":
            continue
        pos = m.get("pos") or {}
        if isinstance(pos, dict) and isinstance(pos.get("line"), int):
            out.append(pos["line"])
    return out


def goals_of(messages: Sequence[dict[str, Any]]) -> list[str]:
    """The goal text Lean reports still open, in report order."""

    out = []
    for m in messages:
        data = str(m.get("data", "")).strip()
        if m.get("severity") == "error" and data.startswith(UNSOLVED):
            body = data[len(UNSOLVED):].strip()
            if body:
                out.append(body)
    return out


SYSTEM = """You extend a Lean 4 proof one step at a time against a full Mathlib.

You are shown one open goal and every step already proved for it. Write the rest of the proof as a
chain of `have` steps in one ```lean block, each step small enough that Lean
accepts it on its own. Every step that compiles is kept permanently, so a long
guess costs nothing but a short correct prefix is worth a lot.

Rules:
- A HAVE must be a step you are confident Lean accepts on its own. Small is better.
- Never write sorry, admit, axiom, native_decide, or unsafe.
- Prefer omega, decide, interval_cases, norm_num, linarith, nlinarith, ring, simp.
- ℕ subtraction truncates. Prove the side condition and let omega restate the
  hypothesis with the subtracted term moved across, so no `-` is left."""


def ask_user(problem: Problem, slot: Slot, goal: str) -> str:
    proved = "\n".join(f"have {k} := by {t}" for k, t in slot.steps) or "(nothing yet)"
    return "\n".join([
        f"Problem: {problem.id}", "", "Statement:", problem.description, "",
        "Challenge file:", "```lean", problem.challenge, "```", "",
        "Already proved for this slot:", "```lean", proved, "```", "",
        "The goal Lean still reports open:", "```", goal, "```",
        *( ["", "Your last attempt and what Lean said about it:",
            "```", slot.last[0][:400], "```", "```", slot.last[1], "```"]
           if slot.last[1] else [] ),
        *( [f"", f"Already rejected: {'; '.join(sorted(slot.tried)[:6])}"]
           if slot.tried else [] ),
    ])


def offered_steps(reply: str, indent: str) -> tuple[list[tuple[str, str]], str]:
    """Split a whole proof into top-level `have` steps and whatever closes it.

    Models write the entire proof, so harvest its longest compiling prefix."""

    block = re.search(r"```(?:lean)?\n(.*?)```", reply, re.S)
    body = block.group(1) if block else reply
    lines = [l for l in body.splitlines() if l.strip()]
    base = min((len(l) - len(l.lstrip()) for l in lines), default=0)
    steps, tail, current = [], [], None
    for line in lines:
        depth = len(line) - len(line.lstrip())
        head = HAVE_HEAD.match(line) if depth <= base else None
        if head:
            if current:
                steps.append(current)
            current = (head.group(1).strip(), head.group(2).strip())
            continue
        if current and depth > base:
            current = (current[0], f"{current[1]}\n{indent}  {line.strip()}")
            continue
        if current:
            steps.append(current)
            current = None
        if depth <= base and not line.lstrip().startswith(("theorem", "import", "--")):
            tail.append(line.strip())
    if current:
        steps.append(current)
    return steps, " ".join(tail[-1:])



@dataclass
class Config:
    lines: tuple[str, ...]
    budget_usd: float
    time_limit_s: float
    headroom: float = 0.9


class Blackboard:
    """Keeps proved steps, and only ever adds to them."""

    def __init__(self, config: Config):
        self.config = config
        self._deadline = 0.0
        self._spent = 0.0

    def _left(self) -> float:
        return self._deadline - time.monotonic()

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        cfg = self.config
        started = time.monotonic()
        self._deadline = started + cfg.time_limit_s
        names = answer_names(problem.challenge)
        slots = find_slots(problem.challenge)
        events: list[dict[str, Any]] = []
        model_turn = 0
        stuck = 0

        source, _ = render(problem.challenge, slots)
        try:
            while self._left() > TURN_RESERVE_S and not all(s.done for s in slots):
                if self._spent >= cfg.headroom * cfg.budget_usd:
                    events.append({"stage": "stop", "note": "budget headroom"})
                    break
                progressed = False
                for slot in slots:
                    if slot.done or self._left() <= TURN_RESERVE_S:
                        continue
                    got = await self._advance(problem, slots, slot, services,
                                              events, names, model_turn)
                    model_turn += 1
                    progressed = progressed or got
                stuck = 0 if progressed else stuck + 1
                if stuck >= STUCK_LIMIT:
                    events.append({"stage": "stop", "note": "no slot advanced"})
                    break
            source, _ = render(problem.challenge, slots)
            check = await services.lean.check_file(source)
            if check.accepted and not scoring_faults(source, names, problem.challenge):
                services.checkpoint(source, {"stage": "closed"})
                events.append({"stage": "accepted"})
        except Exception as exc:  # noqa: BLE001
            events.append({"stage": "stop", "note": f"{type(exc).__name__}: {exc}"[:200]})

        final, _ = render(problem.challenge, slots)
        if banned_constructs(final):
            final = problem.challenge
        return AgentResult(final, {
            "steps": {str(s.line): len(s.steps) for s in slots},
            "closed": sum(1 for s in slots if s.done), "slots": len(slots),
            "spend_usd": round(self._spent, 6),
            "wall_s": round(time.monotonic() - started, 1), "events": events,
        })

    async def _advance(self, problem, slots, slot, services, events, names, turn) -> bool:
        """One attempt at one slot. Anything accepted here is permanent."""

        source, spans = render(problem.challenge, slots)
        check = await services.lean.check_file(source)
        span = spans[slot.line]
        goals = goals_of(check.messages)
        slot.goal = goals[0] if goals else slot.goal
        if slot.is_answer:
            return await self._answer(problem, slots, slot, services, events, names, turn)
        for tactic in self._free_closers():
            if tactic in slot.tried:
                continue
            if await self._try(problem, slots, slot, services, names, events, closer=tactic):
                events.append({"stage": "closed_free", "line": slot.line, "tactic": tactic[:60]})
                return True
            slot.tried.add(tactic)
            if self._left() <= TURN_RESERVE_S:
                return False
        return await self._ask(problem, slots, slot, services, events, names, turn)

    def _free_closers(self) -> list[str]:
        """One `first` over the cocktail costs a single Lean check and no tokens."""

        return ["first " + " ".join(wrap_tactic(t) for t in COCKTAIL)]

    async def _try(self, problem, slots, slot, services, names, events=None,
                   step=None, closer=None) -> bool:
        """Accept only when nothing inside this slot errors.

        The placeholder `sorry` is banned, so only the offered text is screened."""

        offered = " ".join(step or ()) if step is not None else (closer or "")
        if banned_constructs(offered):
            return False
        before_steps, before_closer = list(slot.steps), slot.closer
        if step is not None:
            slot.steps = before_steps + [step]
        if closer is not None:
            slot.closer = closer
        source, spans = render(problem.challenge, slots)
        if statement_drift(problem.challenge, source):
            slot.steps, slot.closer = before_steps, before_closer
            return False
        check = await services.lean.check_file(source)
        lo, hi = spans[slot.line]
        inside = [l for l in error_lines(check.messages) if lo <= l <= hi]
        ok = not inside if closer is None else (check.accepted and not inside)
        if not ok:
            slot.last = (offered, "\n".join(error_messages(check.messages)[:2])[:600])
            if events is not None:
                events.append({"stage": "rejected", "line": slot.line,
                               "kind": "closer" if closer is not None else "step",
                               "inside": len(inside), "accepted": bool(check.accepted)})
            slot.steps, slot.closer = before_steps, before_closer
            return False
        slot.last = ("", "")
        if closer is not None:
            services.checkpoint(source, {"line": slot.line, "closer": True})
        return True

    async def _ask(self, problem, slots, slot, services, events, names, turn) -> bool:
        """Keep the longest prefix of the model's proof that Lean accepts."""

        model = self.config.lines[turn % len(self.config.lines)]
        reply = await self._call(model, SYSTEM, ask_user(problem, slot, slot.goal),
                                 services, events)
        if reply is None:
            return False
        steps, tail = offered_steps(reply, slot.indent)
        gained = 0
        for step in steps:
            if self._left() <= TURN_RESERVE_S:
                break
            if not await self._try(problem, slots, slot, services, names, events, step=step):
                slot.tried.add(step[0][:60])
                break
            gained += 1
            events.append({"stage": "step", "line": slot.line, "model": model,
                           "steps": len(slot.steps)})
        close = _last(CLOSE, reply)
        closer = close.group(1).strip().splitlines()[0] if close else tail
        if closer and await self._try(problem, slots, slot, services, names,
                                      events, closer=closer):
            events.append({"stage": "closed", "line": slot.line, "model": model})
            return True
        return gained > 0

    async def _answer(self, problem, slots, slot, services, events, names, turn) -> bool:
        model = self.config.lines[turn % len(self.config.lines)]
        reply = await self._call(
            model, "Reply with one line, `ANSWER: <plain decimal literal>`.",
            ask_user(problem, slot, "the value this abbrev must take"), services, events)
        if reply is None:
            return False
        found = ANSWER.search(reply)
        if not found:
            return False
        slot.answer = found.group(1)
        source, _ = render(problem.challenge, slots)
        _, bad = numeric_answers_are_literals(source, tuple(names))
        if bad:
            slot.answer = None
            return False
        events.append({"stage": "answer", "line": slot.line, "value": found.group(1)})
        return True

    async def _call(self, model, system, user, services, events) -> str | None:
        try:
            response = await services.llm.complete(
                model=model,
                messages=[{"role": "system", "content": system},
                          {"role": "user", "content": user}],
                max_tokens=STEP_TOKENS, temperature=0.4,
                reasoning={"effort": "medium"},
            )
        except LLMCallError as exc:
            events.append({"stage": "llm_error", "note": str(exc)[:160]})
            raise
        cost = (response.usage or {}).get("cost")
        if isinstance(cost, (int, float)):
            self._spent += float(cost)
        return response.content or None


def create_agent():
    import os
    lines = tuple(m.strip() for m in os.environ.get(
        "VM_LINES", "qwen/qwen3.5-flash-02-23,openai/gpt-oss-120b").split(",") if m.strip())
    return Blackboard(Config(
        lines=lines,
        budget_usd=float(os.environ.get("VM_BUDGET_USD", "1.0")),
        time_limit_s=float(os.environ.get("VM_TIME_LIMIT_S", "1800")) * 0.9,
    ))
