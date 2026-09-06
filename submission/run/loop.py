"""One worker's turn, and the loop that repeats it.

`turn` is the part written out on purpose: a sequence of gates under one lock,
each cheap rung guarded by its own flag. What is not a gate is named instead:
`plan_and_fork`, `post_reply`, and `apply`'s one method per kind of edit."""

from __future__ import annotations
import asyncio
from typing import Any

from re_harness import LLMCallError
from re_harness.budget import BudgetAccountingError, BudgetExceeded
from re_harness.lean import LeanRuntimeError
from submission.config import FEEDBACK_CHARS
from submission.contract import format_messages
from submission.techniques import technique_card
from submission.framework import classify, insert_above, render, restate
from submission.framework_agent import FILE_CHARS, GOAL_CHARS
from submission.prompts import FRAMEWORK_SYSTEM, sheet_for
from submission.state import Feedback, State
from submission.board.reply import interpret, salvage
from submission.board.text import proved_facts, restates, settled_inside, view
from submission.board.types import Board, Edit, Goal, step_tokens
from submission.run.asking import Asking
from submission.run.blackboard import BEAM, WITHDRAW_AFTER, Blackboard
from submission.run.budget import Budget
from submission.run.context import Run
from submission.run.delivery import Delivery
from submission.run.ladder import Ladder


# `FRAMEWORK_SYSTEM`, less "give every have a body": on the board a
# `have` may end in `sorry` and becomes a goal of its own.
BOARD_SYSTEM = FRAMEWORK_SYSTEM.replace(
    "  obtain, subst, left, right, exfalso, interval_cases, by_contra, show, rw.\n"
    "  A reshaping step goes alone, because it changes the goal for everything after.\n"
    "- it asserts a new fact: a `have`. Give every `have` a body. Independent `have`s\n"
    "  may be sent together; Lean names each one that fails.",
    "  obtain, subst, left, right, exfalso, interval_cases, by_contra, show, rw.\n"
    "  A reshaping step goes alone, because it changes the goal for everything after.\n"
    "- it asserts a new fact: a `have`. A `have` whose proof is short gets its body;\n"
    "  one whose proof is long ends in `:= by sorry` and becomes a goal on the board,\n"
    "  proved in its own turn. When the proof left is more than about twenty lines,\n"
    "  post its facts this way and prove one of them, do not write it all at once:\n"
    "  a reply that runs past the token limit keeps only its complete steps.")
BOARD_SYSTEM = BOARD_SYSTEM + "\n\n" + technique_card()
assert "goal on the board" in BOARD_SYSTEM
# Two rejections on a goal buy it a plan from the other model, as before.
PLAN_AFTER = 2
# Library probes (`apply?`, the name scan) wait for one rejected step.
SEARCH_AFTER = 1
# A worker with no goal to take waits this long for the board to change.
IDLE_WAIT_S = 2.0


class Loop:
    def __init__(self, agent: Any, run: Run, budget: Budget, bb: Blackboard,
                 asking: Asking, ladder: Ladder, delivery: Delivery) -> None:
        self.agent, self.run, self.budget = agent, run, budget
        self.bb, self.asking, self.ladder, self.delivery = bb, asking, ladder, delivery
        self.lock = asyncio.Lock()
        self.finished = False
        # Every plan asked for a declaration, kept across restarts: the next
        # plan is asked to differ from them.
        self.routes: dict[str, list[str]] = {}

    async def apply(self, author: str, goal: Goal, edits: list[Edit]) -> bool:
        """Every edit a reply asked for, each against the board as it stands.
        Five kinds; only three of them can put anything on the board."""

        took = False
        for edit in edits:
            here = self.bb.board.find(goal.key)
            if edit.kind == "probe":
                await self.run_probe(author, goal, edit)
            elif edit.kind == "drop":
                self.refuse_redeclared(author, goal, edit)
            elif edit.kind == "step":
                took |= await self.post_step(author, goal, here, edit)
            elif edit.kind == "hoist":
                took |= await self.post_lemma(author, goal, edit)
            elif edit.kind == "prove":
                took |= await self.reroute(author, goal, here, edit)
        return took

    async def run_probe(self, author: str, goal: Goal, edit: Edit) -> None:
        """What Lean prints for the expression the reply asked about, handed back
        to its author as this goal's feedback."""

        printed = await self.agent._probe(State(text=self.bb.board.text), edit.body, self.run.services)
        self.run.notes[goal.key].said = Feedback(author, printed, "probe")
        self.run.events.append({"kind": "probe", "by": author, "printed": printed[:80]})

    def refuse_redeclared(self, author: str, goal: Goal, edit: Edit) -> None:
        """A name the file already declares. Nothing is written; the reply is told
        to work the goal it was shown."""

        self.run.events.append({"kind": "drop", "by": author, "name": edit.name})
        self.run.notes[goal.key].reject(
            author, f"`{edit.name}` is already declared; work the goal "
            "you were shown, do not restate it")

    async def post_step(self, author: str, goal: Goal, here: Goal | None, edit: Edit) -> bool:
        """One step at the goal it was written for. Three things a step can be are
        answered without asking Lean: a repeat, a withdrawn claim restated, and
        a fact the declaration already proved."""

        if here is None:
            self.run.events.append({"kind": "stale", "by": author})
            return False
        if edit.body in self.run.notes[here.key].refused:
            # Measured on p10: five byte-identical replies in a row.
            self.run.events.append({"kind": "repeat", "by": author})
            self.run.notes[here.key].repeated.add(author)
            self.run.notes[goal.key].reject(
                author, "that is byte for byte the step already rejected "
                "on this goal; Lean will say the same thing. Try a "
                "different route: " + self.run.notes[goal.key].said.text[:600]
                if self.run.notes[goal.key].said else "that step was already rejected here")
            return False
        # Measured on p09: a substring match locked a worker out for 19
        # min once `n % 3 = 0` was withdrawn and the goal read `⊢ n % 3 = 0`.
        # Only a `have` stating the claim again is a restatement.
        if restates(edit.body, self.bb.withdrawn.get(here.decl, ())):
            self.run.events.append({"kind": "restated", "by": author})
            self.run.notes[goal.key].reject(author, "that step restates a fact "
                                            "already withdrawn from this declaration")
            return False
        present = proved_facts(self.bb.board.text, here)
        if restates(edit.body, present):
            # Measured on p09: the same claim proved twice in one declaration.
            names = [present[c] for c in present if restates(edit.body, [c])]
            self.run.events.append({"kind": "restated", "by": author, "of": names[:3]})
            self.run.notes[goal.key].reject(author, "that step states a fact already "
                                            "on the board as " + ", ".join(f"`{n}`" for n in names[:3])
                                            + "; use it, do not prove it again")
            return False
        nxt, why = await self.ladder.lift_and_advance(self.bb.board, here, edit.body, author)
        if nxt is None:
            self.run.notes[here.key].refused.add(edit.body)
        self.run.events.append({"kind": "step", "by": author, "accepted": nxt is not None,
                       **({} if nxt is not None else {"why": str(why)[:160]})})
        if nxt is None:
            self.run.notes[goal.key].reject(author, why)
            return False
        await self.bb.commit(nxt)
        return True

    async def post_lemma(self, author: str, goal: Goal, edit: Edit) -> bool:
        """A lemma lifted above the graded declaration, audited before it enters the
        file, then its own first step if the reply sent one."""

        took = False
        lifted = await self.bb.look(insert_above(self.bb.board.text, self.run.first_graded, edit.block))
        kept = not classify(lifted.messages)[3]
        # Measured on putnam_2020_a2: a hoisted lemma was false at j = 0;
        # its statement is audited like a `have` before it enters the file.
        bad = await self.asking.audit(author, self.bb.board, lifted) if kept else ""
        kept = kept and not bad
        self.run.events.append({"kind": "lemma", "by": author, "name": edit.name,
                       "accepted": kept})
        if not kept:
            self.run.notes[goal.key].reject(
                author, bad or format_messages(lifted.messages)[:FEEDBACK_CHARS])
            return took
        await self.bb.commit(lifted)
        took = True
        fresh = next((g for g in self.bb.board.goals if g.decl == edit.name), None)
        if fresh and edit.body.strip():
            nxt, why = await self.asking.advance(self.bb.board, fresh, edit.body, author)
            self.run.events.append({"kind": "step", "by": author, "accepted": nxt is not None,
                       **({} if nxt is not None else {"why": str(why)[:160]})})
            if nxt is not None:
                await self.bb.commit(nxt)
            else:
                self.run.notes[fresh.key].said = Feedback(author, why)
        return took

    async def reroute(self, author: str, goal: Goal, here: Goal | None, edit: Edit) -> bool:
        """A named declaration re-proved from its statement, and the fallback for a
        header that was only an echo of the goal already in hand."""

        # The whole proof of a named declaration replaces what it had.
        # Measured on p09: appended, it doubled its own opening; dropped,
        # it was the best turn of the run.
        fresh_text, at = restate(self.bb.board.text, edit.name)
        if at < 0:
            return False
        opened = await self.bb.look(fresh_text)
        target = opened.goals[at] if at < len(opened.goals) else None
        self.run.events.append({"kind": "route", "by": author, "to": edit.name})
        if target is None:
            return False
        nxt, why = await self.asking.advance(opened, target, edit.body, author)
        if nxt is None and here is not None and edit.name == here.decl:
            # The header was an echo and the body continues from here.
            nxt, why = await self.asking.advance(self.bb.board, here, edit.body, author)
        self.run.events.append({"kind": "step", "by": author, "accepted": nxt is not None,
                       **({} if nxt is not None else {"why": str(why)[:160]})})
        if nxt is None:
            self.run.notes[goal.key].reject(author, why)
            return False
        await self.bb.commit(nxt)
        return True

    def prompt_for(self, goal: Goal, model: str, skeleton: bool = False,
                   plan: str | None = None) -> str:
        source, line = view(*render(self.bb.board.text, self.bb.board.index(goal))[:1], goal.decl)
        plan = self.run.notes[goal.key].plan if plan is None else plan
        parts = [f"Problem: {self.run.problem.description}".strip(),
                 "File:\n" + source[-FILE_CHARS:],
                 "What Lean reports as open, with its hypotheses. The first goal "
                 f"is the active one, at `skip` on line {line}:\n"
                 f"{goal.text[:GOAL_CHARS]}"]
        if self.run.notes[goal.key].hint:
            parts.append(self.run.notes[goal.key].hint)
        sheet = "\n".join(x for x in (sheet_for(goal.text), self.run.notes[goal.key].shelved) if x)
        if sheet:
            parts.append("Names the loaded Mathlib has for this goal's vocabulary, "
                         f"as #check prints them:\n{sheet}")
        if plan:
            parts.append("A mathematician was asked how to prove this goal and "
                         f"answered:\n{plan}")
        if self.run.notes[goal.key].said:
            parts.append(f"{self.run.notes[goal.key].said.lead(model)}:\n{self.run.notes[goal.key].said.text}")
        if skeleton:
            # Measured on rmo_2001_2: the plan was right at t=173 and both
            # models then tried to write all of it in one reply, 37 times
            # past the token cap. The plan goes on the board as statements.
            parts.append("Write the plan as a skeleton: one `have` per fact "
                         "in the order the plan uses them, each with the "
                         "statement in full and the body `:= by sorry`, then "
                         "the one tactic line that closes the goal from those "
                         "facts. Do not prove any fact here; each becomes a "
                         "goal of its own.")
        parts.append("Reply with one ```lean code block containing only tactic "
                     "lines, and nothing before or after it. No explanation.")
        return "\n\n".join(parts)

    async def turn(self, model: str) -> bool:
        """One turn for one worker: False when there was no goal to take."""

        async with self.lock:
            if any(self.delivery.done_text(b) is not None for b in self.bb.branches):
                self.finished = True
                return True
            if self.bb.all_last_in_line() or self.bb.stalled() or self.bb.exhausted():
                drained = self.bb.exhausted()
                await self.ladder.unstick()
                if drained:
                    # The board moved (or could not): the models may be
                    # asked once more, with the new feedback in front of them.
                    self.run.notes.forget_repeats()
            picked = self.bb.pick(model)
            goal = picked[1] if picked else None
            if picked:
                self.bb.focus(picked[0])
            base = self.bb.board
            if goal is not None and goal.stmt in self.bb.proven and not self.run.notes[goal.key].recalled:
                self.run.notes[goal.key].recalled = True
                nxt, _ = await self.asking.judge(base, goal, self.bb.proven[goal.stmt])
                if nxt is not None:
                    self.run.events.append({"kind": "recall", "goal": goal.text[-120:]})
                    await self.bb.commit(nxt)
                    return True
            if goal is not None and not self.run.notes[goal.key].swept:
                self.run.notes[goal.key].swept = True
                if await self.ladder.sweep(goal) or await self.ladder.leaf_sweep(goal) or await self.ladder.witness_sweep(goal) \
                        or await self.ladder.generalise_sweep(goal):
                    return True
            if goal is not None and not self.run.notes[goal.key].searched \
                    and self.run.notes[goal.key].tries >= SEARCH_AFTER:
                # Measured over 70 runs: `apply?` and the name scan took
                # 19% of the wall clock under the lock (601 probes, 22
                # goals closed; 269 scans at 22 s), and Lean is busy
                # 60-74% of a run. A goal the first step closes never pays.
                self.run.notes[goal.key].searched = True
                if await self.ladder.library_sweep(goal):
                    return True
                await self.asking.consult(goal)
            if goal is not None:
                self.run.notes.claim(goal.key, model)
                wants_plan = (self.run.notes[goal.key].tries >= PLAN_AFTER
                              and not self.run.notes[goal.key].plan)
                prompt = self.prompt_for(goal, model)
        if goal is not None and wants_plan:
            goal, prompt = await self.plan_and_fork(model, goal, base)
            if not prompt:
                async with self.lock:
                    self.run.notes.release(goal.key, model)
                return True
        if goal is None:
            return False
        task = asyncio.ensure_future(
            self.agent._call(model, prompt, step_tokens(model), self.run.services, self.run.ledger, system=BOARD_SYSTEM))
        self.run.loose.append(task)
        try:
            reply, why = await task
        finally:
            self.run.loose.remove(task)
        await self.post_reply(model, goal, base, reply, why)
        return True

    async def plan_and_fork(self, model: str, goal: Goal, base: Board) -> tuple[Goal, str]:
        """Two plans for a goal that has been refused twice, and a sibling branch
        carrying the second one. Returns the goal where it now sits and the prompt
        to send, or "" for a prompt when the goal is gone from the board."""

        # The crux is where routes diverge, so it gets two: one plan
        # from each model, the second written as a skeleton onto a
        # sibling branch. Lean's progress on each decides between them.
        other = next((m for m in self.run.cfg.lines if m != model), model)
        state = State(text=self.bb.board.text, goal=goal.text)
        avoid = list(self.routes.get(goal.decl, []))
        plan, second = await asyncio.gather(
            self.agent._ask_plan(self.run.problem, state, self.run.services, self.run.ledger, other, avoid=avoid),
            self.agent._ask_plan(self.run.problem, state, self.run.services, self.run.ledger, model, avoid=avoid))
        ask_second, fork = "", None
        async with self.lock:
            self.run.notes[goal.key].plan = plan
            self.routes.setdefault(goal.decl, []).extend(
                p for p in (plan, second) if p.strip())
            self.run.events.append({"kind": "plan", "by": other, "chars": len(plan)})
            self.run.events.append({"kind": "plan", "by": model, "chars": len(second)})
            now = self.bb.live(base.bid)
            moved = now.find(goal.key) if now else None
            if moved:
                self.bb.focus(now)
                goal = moved
            prompt = self.prompt_for(goal, model, skeleton=True) if moved else ""
            if prompt:
                self.run.events.append({"kind": "skeleton", "by": model})
            if moved and second.strip() and second.strip() != plan.strip() \
                    and len(self.bb.branches) < BEAM + 1:
                fork = self.bb.fork(now)
                if fork is not None:
                    ask_second = self.prompt_for(goal, model, skeleton=True, plan=second)
                self.bb.focus(now)
        if ask_second and fork is not None:
            reply_b, _ = await self.agent._call(model, ask_second, step_tokens(model),
                                          self.run.services, self.run.ledger, system=BOARD_SYSTEM)
            async with self.lock:
                side = self.bb.live(fork.bid)
                there = side.find(goal.key) if side else None
                took = False
                if there is not None:
                    self.bb.focus(side)
                    edits = interpret(reply_b, self.bb.board, there, self.run.graded)
                    took = await self.apply(model, there, edits) if edits else False
                if took and self.bb.live(fork.bid):
                    self.run.events.append({"stage": "route", "from": base.bid,
                                   "to": fork.bid, "by": model})
                    self.bb.prune()
                else:
                    self.bb.discard(fork.bid)
                main = self.bb.live(base.bid)
                if main:
                    self.bb.focus(main)
        return goal, prompt

    async def post_reply(self, model: str, goal: Goal, base: Board,
                         reply: str, why: str) -> None:
        """What a step reply does to the board: salvaged if it was cut, forked if
        the goal moved on under it, posted if it still fits, and the goal withdrawn
        once too many turns have gone into it."""

        async with self.lock:
            self.run.notes.release(goal.key, model)
            if why == "length":
                reply = salvage(reply)
                kept = reply.count("\n") + 1 if reply else 0
                self.run.events.append({"kind": "cut", "by": model, "kept": kept})
                if not kept:
                    self.run.notes[goal.key].reject(model, self.run.notes[goal.key].said.text
                                                    if self.run.notes[goal.key].said else "nothing yet", "cut")
                    return
            now = self.bb.live(base.bid)
            here = now.find(goal.key) if now else None
            if here is not None:
                self.bb.focus(now)
            # The goal moved on under this reply. Judged against the file it
            # was asked about, an accepted answer is a second way forward, and
            # a second way is a branch, not waste. With the beam full there is
            # no room for one, and the reply is stale.
            elif base.find(goal.key) is not None and (fork := self.bb.fork(base)) is not None:
                here = fork.find(goal.key)
                edits = interpret(reply, self.bb.board, here, self.run.graded)
                took = await self.apply(model, here, edits) if edits else False
                if took and self.bb.live(fork.bid):
                    self.run.events.append({"stage": "fork", "from": base.bid, "to": fork.bid,
                                   "goal": goal.text[:60]})
                    self.bb.prune()
                else:
                    self.bb.discard(fork.bid)
                    self.run.events.append({"kind": "stale", "by": model})
                return
            if here is None:
                self.run.events.append({"kind": "stale", "by": model})
                return
            edits = interpret(reply, self.bb.board, here, self.run.graded)
            if not edits:
                self.run.events.append({"kind": "empty", "by": model})
                self.run.notes[goal.key].reject(model, self.run.notes[goal.key].said.text
                                                if self.run.notes[goal.key].said else "nothing yet", "empty")
                return
            await self.apply(model, here, edits)
            still = self.bb.board.find(goal.key)
            if still is not None and self.run.notes[goal.key].tries >= WITHDRAW_AFTER:
                if settled_inside(self.bb.board.text, still) >= 2 and not self.run.notes[still.key].leaf_restarted:
                    # Measured on rmo_2000_6 (win54): one stuck case took the
                    # have with h2a, h5a and 2 closed cases down. The leaf
                    # restarts once before proved work is withdrawn.
                    self.run.notes[still.key].leaf_restarted = True
                    self.run.notes.forget(still.key)
                    self.run.events.append({"kind": "leaf_restart", "by": model, "goal": still.text[-160:],
                                   "settled": settled_inside(self.bb.board.text, still)})
                else:
                    await self.bb.take_back(model, still)


    async def worker(self, model: str) -> None:
        idle, faults = 0, 0
        while self.budget.time_left() > 0 and self.budget.can_ask() and not self.finished:
            try:
                if await self.turn(model):
                    idle = 0
                else:
                    idle += 1
                    if idle > 3 and not self.run.notes.busy() and not self.bb.board.goals:
                        self.run.events.append({"stage": "stop", "note": "no goal left to work on"})
                        return
                    try:
                        await asyncio.wait_for(self.bb.changed.wait(), IDLE_WAIT_S)
                    except asyncio.TimeoutError:
                        pass
            except (BudgetExceeded, BudgetAccountingError, LeanRuntimeError, LLMCallError):
                raise
            except Exception as exc:  # noqa: BLE001 - one bad turn must not zero the problem
                faults += 1
                self.run.events.append({"stage": "worker_error", "by": model,
                               "error": f"{type(exc).__name__}: {exc}"[:200]})
                if faults >= 3:
                    return
