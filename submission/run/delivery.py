"""What we would hand in if the run were killed now, and the final check
before handing anything in. Depends on `budget` for the clock."""

from __future__ import annotations
import re

from re_harness import AgentResult
from re_harness import Services
from submission.techniques import PREAMBLE_END
from submission.framework import (alternatives, axiom_probe, classify, collapse, cursor_goal,
                                  drop_lines, first_blocks, have_spans, is_done, placeholders, render)
from submission.contract import grade, scoring_faults
from submission.replies import lighter_forms
from submission.state import State
from submission.cells import modular, strip_markers
from submission.techniques import PREAMBLE_MARK, strip_techniques, uses_techniques
from submission.board.types import Board
from submission.board.text import shed_unreferenced
from submission.run.budget import Budget
from submission.run.context import Run

# The comparator allows 180 seconds, so a file that only just compiles here is
# not safe there. Recorded, never silently accepted.
SLOW_COMPILE_MS = 150_000


class Delivery:
    def __init__(self, run: Run, budget: Budget) -> None:
        self.run, self.budget = run, budget
        self.best = run.text
        self.shed_named: set[str] = set()

    def offer(self, candidate: str, accepted: bool) -> None:
        if accepted or not scoring_faults(candidate, self.run.names, self.run.problem.challenge):
            self.best = candidate
            # The checkpoint is what a killed run is graded on: cells as
            # declarations, each within its own budget.
            self.run.services.checkpoint(modular(self.best, self.run.cells) if "-- cell " in self.best else self.best,
                                {"accepted": accepted})

    def done_text(self, b: Board) -> str | None:
        """The finished file: accepted with nothing open, or sound (no
        failure beyond its open goals) with every open goal inside a helper
        nothing graded uses, which is removed. `deliver` checks it again."""
        if b.accepted and is_done(b.text):
            return b.text
        if classify(b.messages).failures:
            return None
        text, shed = shed_unreferenced(b.text, self.run.graded)
        if not shed or not is_done(text) or re.search(r"\bsorry\b", text) \
                or any(g.decl not in shed for g in b.goals):
            return None
        for name in shed:
            if name not in self.shed_named:
                self.shed_named.add(name)
                self.run.events.append({"stage": "shed", "name": name})
        return text

    def result(self, source: str, how: str, accepted: bool) -> AgentResult:
        # Every event, so a run's accounting (who wrote, who audited, what
        # closed without a model) can be read off result.json. A 500-turn
        # run is about 150 KB; the earlier last-60 cut made counts tails.
        return AgentResult(strip_markers(source), {
            "strategy": "board",
            "solved_by": how,
            "accepted_by_repl": accepted,
            "spend_usd": round(self.run.ledger.spent_usd, 6),
            "wall_s": round(self.budget.elapsed(), 1),
            "turns": len(self.run.events),
            "events": list(self.run.events),
        })

    async def deliver(self, text: str, how: str) -> AgentResult | None:
        """The finished file as one declaration per cell; the one-declaration
        form only if that fails to compile."""
        shaped = modular(text, self.run.cells) if "-- cell " in text else strip_markers(text)
        delivered = await self.deliver_form(shaped, how)
        if delivered is None and shaped != strip_markers(text):
            self.run.events.append({"stage": "deliver", "form": "inline"})
            delivered = await self.deliver_form(strip_markers(text), how)
        return delivered

    async def deliver_form(self, text: str, how: str) -> AgentResult | None:
        state = await finish(State(text=text, accepted=True), self.run.services, self.budget.time_left)
        final = state.text
        if not uses_techniques(final):
            # The judge compiles cold, 180 s on 4 cores; a proof that never
            # calls a technique does not carry the block that defines them.
            final = strip_techniques(final)
        check = await self.run.services.lean.check_file(
            axiom_probe(final, self.run.graded))
        faults, _ = grade(final, check, self.run.names, self.run.problem.challenge)
        if (not check.accepted or faults) and final != state.text:
            final = state.text
            check = await self.run.services.lean.check_file(
                axiom_probe(final, self.run.graded))
            faults, _ = grade(final, check, self.run.names, self.run.problem.challenge)
        self.run.events.append({"stage": "verify", "accepted": check.accepted,
                       "faults": faults[:5], "compile_ms": check.duration_ms,
                       "slow": check.duration_ms > SLOW_COMPILE_MS,
                       "techniques": "kept" if PREAMBLE_MARK in final else "dropped"})
        if any("sorry" in f for f in faults):
            shown = final.split("\n")
            self.run.events.append({"stage": "sorry_left", "lines": [
                "\n".join(shown[max(i - 3, 0):i + 1]) for i, l in enumerate(shown) if "sorry" in l][:3]})
        if not check.accepted or faults:
            return None
        self.offer(final, True)
        return self.result(final, how, True)


# The finish pass is free of tokens but not of clock, so it is bounded.
MAX_COLLAPSE = 24


# Measured on p08: a file the REPL checks in 570ms timed out at the comparator's
# 180s, because the kernel there re-checks the term and nlinarith's are huge.
MAX_LIGHTEN = 16


# Below this a proof is already small; tidying it only risks it.
TIDY_ABOVE_BYTES = 2000


def below_header(text: str) -> str:
    """The file without the technique block: the tidy threshold is about the
    proof's size, and the block is the same 1.8 KB in every file."""
    i = text.find(PREAMBLE_END)
    return text[i + len(PREAMBLE_END):] if i >= 0 else text


MAX_DELETIONS = 12


# Each try is one check, and a check is 60ms against a reply's seconds.
MAX_PREFIXES = 8


FINISH_RESERVE_S = 300.0


async def look(text: str, services: Services, focus: int = 0) -> State:
    """One check does both jobs: it adjudicates, and it prints the next goal."""

    open_goals = len(placeholders(text))
    focus = min(max(focus, 0), open_goals - 1) if open_goals else 0
    source, line = render(text, focus)
    check = await services.lean.check_file(source)
    return State(text=text, goal=cursor_goal(check.messages, line), line=line,
                 messages=list(check.messages), accepted=check.accepted,
                 focus=focus, goals=open_goals)


async def finish(state: State, services: Services, time_left) -> State:
    """Shrink a finished file: the comparator recompiles it cold in 180s."""

    # Measured on p08: both passes turned a file the comparator accepted
    # into one it timed out on, because deleting a fact a closer was using
    # makes that closer redo the work in a term the kernel then re-checks.
    # A short file has nothing to win here, and §4 says not to touch it.
    if len(below_header(state.text)) > TIDY_ABOVE_BYTES:
        state = await lighten(state, services, time_left)
        state = await prune(state, services, time_left)
    for _ in range(MAX_COLLAPSE):
        blocks = first_blocks(state.text)
        if not blocks or time_left() < FINISH_RESERVE_S:
            break
        collapsed = None
        for tactic in alternatives(blocks[0].group(2)):
            probe = await look(collapse(state.text, blocks[0], tactic), services)
            if probe.accepted:
                collapsed = probe
                break
        if collapsed is None:
            break
        state = collapsed
    return state


async def lighten(state: State, services: Services, time_left) -> State:
    """Make the finished term small.

    Measured on p08: `nlinarith` with three hints checks in 348ms here and
    times out at the comparator's 180s, with one hint it passes."""

    for rewrite in lighter_forms(state.text)[:MAX_LIGHTEN]:
        if time_left() < FINISH_RESERVE_S:
            break
        probe = await look(rewrite, services)
        if probe.accepted and is_done(probe.text):
            state = probe
    return state


async def prune(state: State, services: Services, time_left) -> State:
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
        probe = await look(
            drop_lines(state.text, range(start, end + 1)), services)
        if probe.accepted and is_done(probe.text):
            state = probe
    return state


