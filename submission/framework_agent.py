"""One file, one cursor, two models taking turns; Lean adjudicates every step.

The loop is FRAMEWORK.md: check, read the goal at `skip`, try the free closers,
otherwise ask a model for one step. A step that compiles is permanent.
"""

from __future__ import annotations

import asyncio
import re
import time
from dataclasses import dataclass, field
from typing import Any, Sequence

from re_harness import AgentResult, LLMCallError, Problem, Services
from re_harness.budget import BudgetAccountingError, BudgetExceeded
from re_harness.lean import LeanRuntimeError

from submission.agent import (
    BUDGET_HEADROOM,
    declared_names,
    FEEDBACK_CHARS,
    RETRY_BACKOFF_S,
    Config,
    Ledger,
    answer_names,
    format_messages,
    grade,
    normalise_imports,
    refused_before_generation,
    scoring_faults,
    split_files,
    strip_fences,
    suggested_tactics,
    suggestions,
    sweep_files,
    usable_cocktail,
)
from submission.framework import (
    alternatives,
    axiom_probe,
    collapse,
    first_blocks,
    have_spans,
    classify,
    cursor,
    cursor_goal,
    drop_lines,
    fill_answer,
    insert_preamble,
    is_done,
    message_line,
    normalise_steps,
    render,
    replace_cursor,
    sweep_body,
)

# A step is a few lines; the file it goes into is the context. Wide replies are
# the failure mode here, not narrow ones.
STEP_TOKENS = 2000
ANSWER_TOKENS = 1200
GOAL_CHARS = 4000
FILE_CHARS = 8000
# Two rejections on one goal and the other model gets it, with Lean's reason.
STALL_BEFORE_SWAP = 2
# The finish pass is free of tokens but not of clock, so it is bounded.
MAX_COLLAPSE = 4
MAX_DELETIONS = 12
FINISH_RESERVE_S = 300.0
# Lean's elaboration budget is deterministic, so raising it is sound; it buys
# that determinism with wall clock, which the comparator caps at 180s.
RAISED_HEARTBEATS = "set_option maxHeartbeats 400000"

FRAMEWORK_SYSTEM = """You extend a Lean 4 proof one step at a time, against a full Mathlib.

The file is complete and checkable at every moment. Every unproved place is
`sorry`, except exactly one, which is `skip`: that is the active goal. You are
asked for the next step at the `skip`, and nothing else.

A step does one of two things:
- it reshapes the goal: intro, induction ... with, constructor, refine, rcases,
  obtain, subst, left, right, exfalso, interval_cases, by_contra, show, rw.
  A reshaping step goes alone, because it changes the goal for everything after.
- it asserts a new fact: a `have`. Give every `have` a body. Independent `have`s
  may be sent together; Lean names each one that fails.

When no closer works, something is missing that the goal does not contain. It is
almost always a witness, a map into a smaller index set, a modulus, an algebraic
identity, a bound that traps a variable, a recurrence, or a case split. Name
which, state it as a `have`, and prove that. When the missing thing is a number,
do not guess it: ask for a `#eval` probe instead.

Rules:
- Never write a lemma name you have not seen Lean accept as a closing term.
  Write the goal and let `exact?` name it. This does not reach `rw` and `simp`
  arguments, which you must write from memory.
- State each fact as small as it can stand on its own.
- When a tactic has failed twice on one goal, restate the goal; do not retry it.
- Anything a later step names must be at the outer level, not inside another
  `have`'s body.
- Copy terms out of the printed goal rather than retyping them: omega and
  linarith atomise syntactically, so spellings must match.

Answer with Lean tactic lines only. No prose, no code fences, no theorem
header, no `sorry`, no `native_decide`. Indent as if at the top level of the
proof; branches of an `induction ... with` end in `sorry` where you have not
worked yet."""

# Section 3 of the framework: what Lean's message does not say. Sent only when
# the message that triggers it appears, which keeps the prompt small.
NOTES: tuple[tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"omega could not"),
     "omega atomises syntactically, so (3*a)^2 and 9*a^2 are different atoms: "
     "state the ring identity as its own `have ... := by ring`. omega also does "
     "not instantiate a quantified fact; apply it yourself first."),
    (re.compile(r"linarith failed"),
     "Every closer before nlinarith is linear or syntactic. For a symmetric "
     "inequality in nonnegative variables the hint is each square times the "
     "variable its difference leaves out: `have : 0 ≤ a * (b - c) ^ 2 := by "
     "positivity`, which needs 0 ≤ a in context. Over ℕ this is vacuous, "
     "because b - c is truncated."),
    (re.compile(r"maximum number of heartbeats"),
     "This is Lean's elaboration budget, not wall clock. Make the step cheaper, "
     "or ask for `set_option maxHeartbeats 400000 in` before the theorem."),
    (re.compile(r"exact\? could not"),
     "exact? only produces closing terms. It will not give you a rw, simp or "
     "refine argument; write those from memory."),
    (re.compile(r"unknown (identifier|constant)|environment does not contain"),
     "The name is wrong or out of scope. Drop it and state the fact you wanted "
     "as a `have`, letting exact? name the lemma."),
    (re.compile(r"simp made no progress"),
     "Membership in a literal Finset opens with `simp only [Finset.mem_insert, "
     "Finset.mem_singleton]`, in a literal Set with `simp only "
     "[Set.mem_insert_iff, Set.mem_singleton_iff]`. The namespaces do not "
     "interchange."),
    (re.compile(r"motive is not type correct|induction"),
     "rcases on an inductively defined Prop loses the induction hypothesis. Use "
     "`induction h with | c₁ ... | c₂ ...`, labelled by constructor name, and "
     "clear hypotheses mentioning the variable first."),
    (re.compile(r"ℕ|Nat\.sub"),
     "ℕ subtraction is truncated. State `b ≤ a` as its own `have` and let omega "
     "move the term across, or move to ℤ."),
)


def notes_for(text: str) -> str:
    """The framework entries this message triggers, and only those."""

    hits = [note for pattern, note in NOTES if pattern.search(text)]
    return "\n".join(f"- {h}" for h in hits[:3])


@dataclass
class Feedback:
    """What to tell the next model, and who earned it."""

    author: str
    text: str
    kind: str = "rejected"

    def lead(self, model: str) -> str:
        if self.kind == "probe":
            return "The probe you asked for printed"
        if self.author == model:
            return "Your last step was rejected and has been removed. Lean said"
        return f"A {self.author} attempt on this goal was rejected. Lean said"


@dataclass
class State:
    """The proof and what the last check said about it."""

    text: str
    goal: str = ""
    line: int = 0
    messages: list[dict[str, Any]] = field(default_factory=list)
    accepted: bool = False


@dataclass
class Turn:
    """One proposal and what became of it."""

    author: str
    kind: str
    accepted: bool
    cost: float = 0.0


class FrameworkAgent:
    def __init__(self, config: Config | None = None):
        self.config = config or Config.from_env()

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        cfg = self.config
        started = time.monotonic()
        deadline = started + cfg.last_turn_start_s
        ledger = Ledger()
        names = answer_names(problem.challenge)
        text = normalise_imports(problem.challenge, problem.challenge)
        best = text
        events: list[dict[str, Any]] = []
        models = list(cfg.lines)
        turn_of = 0
        swept: set[tuple[str, tuple[str, int]]] = set()
        stalls = 0
        feedback: Feedback | None = None
        raised = False

        def time_left() -> float:
            return deadline - time.monotonic()

        def can_ask() -> bool:
            return ledger.spent_usd < BUDGET_HEADROOM * cfg.budget_usd

        def offer(candidate: str, accepted: bool) -> None:
            """Only ever checkpoint a file the grader could score."""

            nonlocal best
            if accepted or not scoring_faults(candidate, names, problem.challenge):
                best = candidate
                services.checkpoint(best, {"accepted": accepted})

        def result(source: str, how: str, accepted: bool) -> AgentResult:
            return AgentResult(source, {
                "strategy": "framework",
                "solved_by": how,
                "accepted_by_repl": accepted,
                "spend_usd": round(ledger.spent_usd, 6),
                "wall_s": round(time.monotonic() - started, 1),
                "turns": len(events),
                "events": events[-60:],
            })

        try:
            cocktail = await usable_cocktail(services)
            for candidate in sweep_files(problem.challenge, cocktail) + split_files(
                    problem.challenge, cocktail):
                if time_left() <= 0:
                    break
                check = await services.lean.check_file(candidate)
                if check.accepted and not scoring_faults(candidate, names, problem.challenge):
                    offer(candidate, True)
                    events.append({"stage": "sweep", "accepted": True})
                    return result(candidate, "deterministic_sweep", True)

            if names and can_ask():
                text = await self._resolve_answers(
                    problem, text, names, services, ledger, events)

            state = await self._look(text, services)
            while time_left() > 0:
                if state.accepted and is_done(state.text):
                    break
                if is_done(state.text) or state.accepted:
                    state = await self._settle(state, services)
                    continue

                # Never re-run a closer on a goal whose text and file are both
                # unchanged; a longer file is a changed context.
                seen = (state.goal, len(state.text))
                if state.goal and ("closers", seen) not in swept:
                    block, kind, author = sweep_body(cocktail), "closers", "harness"
                    swept.add(("closers", seen))
                elif state.goal and ("search", seen) not in swept:
                    block, kind, author = "exact?", "search", "harness"
                    swept.add(("search", seen))
                elif can_ask():
                    author = models[turn_of % len(models)]
                    block = await self._ask_step(
                        problem, state, feedback, author, services, ledger)
                    kind = "step"
                    if not block:
                        turn_of += 1
                        continue
                    if is_probe(block):
                        printed = await self._probe(state, block, services)
                        feedback = Feedback(author, printed, "probe")
                        events.append({"kind": "probe", "by": author, "printed": printed[:80]})
                        continue
                else:
                    events.append({"stage": "stop", "note": "budget headroom"})
                    break

                nxt, why = await self._advance(state, block, services)
                if nxt is None and why == HEARTBEAT_RETRY and not raised:
                    # A step that only ran out of elaboration budget is not a
                    # wrong step; give it the budget once and re-adjudicate.
                    raised = True
                    state = await self._look(
                        insert_preamble(state.text, RAISED_HEARTBEATS), services)
                    nxt, why = await self._advance(state, block, services)
                events.append({"kind": kind, "by": author, "accepted": nxt is not None})
                if nxt is None:
                    # Only a model's own rejections count towards its turn; the
                    # free attempts are the harness's.
                    feedback = Feedback(author if kind == "step" else kind, why)
                    stalls += 1 if kind == "step" else 0
                    if stalls >= STALL_BEFORE_SWAP:
                        turn_of += 1
                        stalls = 0
                    continue
                state, feedback, stalls = nxt, None, 0
                offer(state.text, state.accepted and is_done(state.text))

            if is_done(state.text):
                state = await self._finish(state, services, time_left)
                probed = axiom_probe(state.text, declared_names(problem.challenge))
                check = await services.lean.check_file(probed)
                faults, _ = grade(state.text, check, names, problem.challenge)
                events.append({"stage": "verify", "accepted": check.accepted,
                               "faults": faults[:5]})
                if check.accepted and not faults:
                    offer(state.text, True)
                    return result(state.text, "framework_loop", True)
            offer(state.text, False)
            return result(best, "best_effort", False)
        except (BudgetExceeded, BudgetAccountingError, LeanRuntimeError) as exc:
            events.append({"stage": "abort", "error": type(exc).__name__})
            return result(best, "aborted", False)

    async def _look(self, text: str, services: Services) -> State:
        """One check does both jobs: it adjudicates, and it prints the next goal."""

        source, line = render(text)
        check = await services.lean.check_file(source)
        return State(text=text, goal=cursor_goal(check.messages, line), line=line,
                     messages=list(check.messages), accepted=check.accepted)

    async def _settle(self, state: State, services: Services) -> State:
        """A placeholder Lean has no goal for is surplus, and comes out."""

        surplus = [message_line(m) for m in classify(state.messages)[1]]
        lines = [l for l in surplus if l] or ([state.line] if state.line else [])
        if not lines:
            return State(text=state.text, accepted=state.accepted, messages=state.messages)
        return await self._look(drop_lines(state.text, lines), services)

    async def _advance(self, state: State, block: str,
                       services: Services) -> tuple[State | None, str]:
        """Try one step. Anything but an open goal means the step is discarded."""

        try:
            candidate, _ = replace_cursor(state.text, block)
        except ValueError:
            return None, "no active goal"
        nxt = await self._look(candidate, services)
        _, surplus, expensive, failures = classify(nxt.messages)
        if expensive and not failures:
            return None, HEARTBEAT_RETRY
        if failures or expensive:
            said = format_messages(nxt.messages)[:FEEDBACK_CHARS]
            return None, f"{said}\n{notes_for(said)}".strip()
        if surplus:
            nxt = await self._settle(nxt, services)
        return nxt, ""

    async def _finish(self, state: State, services: Services, time_left) -> State:
        """Take the search out of a finished file: the comparator allows 180s."""

        state = await self._substitute_search(state, services)
        state = await self._prune(state, services, time_left)
        for _ in range(MAX_COLLAPSE):
            blocks = first_blocks(state.text)
            if not blocks or time_left() < FINISH_RESERVE_S:
                break
            collapsed = None
            for tactic in alternatives(blocks[0].group(2)):
                probe = await self._look(collapse(state.text, blocks[0], tactic), services)
                if probe.accepted:
                    collapsed = probe
                    break
            if collapsed is None:
                break
            state = collapsed
        return state

    async def _prune(self, state: State, services: Services, time_left) -> State:
        """Delete facts the finished proof does not use.

        Only sound now: while a `sorry` remains, no deletion can break anything."""

        tried: set[str] = set()
        for _ in range(MAX_DELETIONS):
            if time_left() < FINISH_RESERVE_S:
                break
            spans = [s for s in have_spans(state.text) if s[2] not in tried]
            if not spans:
                break
            start, end, statement = spans[0]
            tried.add(statement)
            probe = await self._look(
                drop_lines(state.text, range(start, end + 1)), services)
            if probe.accepted and is_done(probe.text):
                state = probe
        return state

    async def _substitute_search(self, state: State, services: Services) -> State:
        """Replace each `exact?` with the term it printed, keeping the search
        call when the term does not re-elaborate."""

        if "exact?" not in state.text and "apply?" not in state.text:
            return state
        for term in suggested_tactics(suggestions(state.messages))[:4]:
            probe = await self._look(state.text.replace("exact?", term, 1), services)
            if probe.accepted:
                return probe
        return state

    async def _probe(self, state: State, block: str, services: Services) -> str:
        """A probe sits above the theorem, is read from its own check, and goes."""

        check = await services.lean.check_file(insert_preamble(state.text, block))
        printed = [str(m.get("data", "")).strip() for m in check.messages
                   if isinstance(m, dict) and m.get("severity") in ("info", "information")]
        return "\n".join(printed)[:FEEDBACK_CHARS] or "nothing"

    async def _ask_step(self, problem: Problem, state: State,
                        feedback: tuple[str, str] | None, model: str, services: Services, ledger: Ledger) -> str:
        source, line = render(state.text)
        parts = [f"Problem: {problem.description}".strip(),
                 "File:\n" + source[-FILE_CHARS:],
                 f"The active goal is at `skip` on line {line}:\n{state.goal[:GOAL_CHARS]}"]
        if feedback:
            parts.append(f"{feedback.lead(model)}:\n{feedback.text}")
        parts.append("Write the next step.")
        reply = await self._call(model, "\n\n".join(parts), STEP_TOKENS, services, ledger)
        return screen_step(reply)

    async def _resolve_answers(self, problem: Problem, text: str, names: Sequence[str],
                               services: Services, ledger: Ledger,
                               events: list[dict[str, Any]]) -> str:
        """An answer slot is a number to compute, never a number to guess."""

        ask = ("Write `#eval` lines, one per name, that compute these answers: "
               f"{', '.join(names)}.\n\nProblem: {problem.description}\n\n"
               f"File:\n{text[:FILE_CHARS]}\n\nLean 4 with Mathlib. Output the "
               "`#eval` lines only. Each must print a single natural number.")
        reply = await self._call(
            self.config.lines[0], ask, ANSWER_TOKENS, services, ledger)
        probes = [l for l in strip_fences(reply).splitlines() if l.strip().startswith("#eval")]
        if not probes:
            return text
        check = await services.lean.check_file(insert_preamble(text, "\n".join(probes)))
        values = [m for m in printed_numbers(check.messages)]
        events.append({"stage": "probe", "values": values[:len(names)]})
        for name, value in zip(names, values):
            text = fill_answer(text, name, value)
        return text

    async def _call(self, model: str, prompt: str, max_tokens: int,
                    services: Services, ledger: Ledger) -> str:
        """Retry only what the provider refused before generating anything."""

        for wait in (0.0,) + RETRY_BACKOFF_S:
            if wait:
                await asyncio.sleep(wait)
            try:
                reply = await services.llm.complete(
                    model=model,
                    messages=[{"role": "system", "content": FRAMEWORK_SYSTEM},
                              {"role": "user", "content": prompt}],
                    max_tokens=max_tokens,
                    temperature=0.4,
                )
            except LLMCallError as exc:
                if refused_before_generation(exc):
                    continue
                raise
            ledger.record(reply.usage)
            return reply.content or ""
        return ""


HEARTBEAT_RETRY = "__heartbeat__"
NUMBER = re.compile(r"^-?\d+$")


def is_probe(block: str) -> bool:
    """A reply that only computes something is a probe, not a step."""

    lines = [l for l in block.splitlines() if l.strip()]
    return bool(lines) and all(l.strip().startswith(("#eval", "#check", "#print"))
                               for l in lines)
STEP_BAN = re.compile(r"^\s*(import|theorem|lemma|example|axiom)\b|```|native_decide|admit",
                      re.M)


def printed_numbers(messages: Sequence[Any]) -> list[str]:
    """What `#eval` printed, in order, keeping only bare numerals."""

    out = []
    for m in messages:
        if isinstance(m, dict) and m.get("severity") in ("info", "information"):
            body = str(m.get("data", "")).strip()
            if NUMBER.match(body):
                out.append(body)
    return out


FENCED = re.compile(r"```(?:lean4?)?\s*\n(.*?)```", re.DOTALL | re.IGNORECASE)


def screen_step(reply: str) -> str:
    """A step is tactic lines. Prose around a fence is dropped, not spliced."""

    blocks = [b for b in FENCED.findall(reply) if b.strip()]
    block = normalise_steps(strip_fences(blocks[-1] if blocks else reply)).strip()
    if not block or STEP_BAN.search(block):
        return ""
    if re.search(r"\bsorry\b", block) and "with" not in block and "|" not in block:
        return ""
    return block


def create_agent() -> FrameworkAgent:
    return FrameworkAgent()
