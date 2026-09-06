"""What we would hand in if the run were killed now, and the final check
before handing anything in. Depends on `budget` for the clock."""

from __future__ import annotations
import re
from typing import Any

from re_harness import AgentResult
from submission.contract import grade, scoring_faults
from submission.cells import modular, strip_markers
from submission.framework import axiom_probe, classify, is_done
from submission.framework_agent import SLOW_COMPILE_MS
from submission.state import State
from submission.techniques import PREAMBLE_MARK, strip_techniques, uses_techniques
from submission.board.types import Board
from submission.board.text import shed_unreferenced
from submission.run.budget import Budget
from submission.run.context import Run


class Delivery:
    def __init__(self, agent: Any, run: Run, budget: Budget) -> None:
        self.agent, self.run, self.budget = agent, run, budget
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
        if classify(b.messages)[3]:
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
        state = await self.agent._finish(State(text=text, accepted=True), self.run.services, self.budget.time_left)
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
