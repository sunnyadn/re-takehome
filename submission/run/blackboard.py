"""The live board: the current file, and the alternatives tried instead.

`Board` in `submission/board/types.py` is one snapshot. It is not frozen, but
it is replaced rather than edited: the only writes to a board are here, on one
`look` has just returned. This holds the current snapshot, the branches racing
beside it, and what each accepted edit did to them."""

from __future__ import annotations
import asyncio
import contextlib
import re
import time

from submission.contract import format_messages
from submission.cells import CELL_PROBE, dissolve, remap, render_check, strip_markers
from submission.framework import (DECL_HEAD, classify, drop_lines, message_line,
                                  proof_span, split_cursor)
from submission.state import Feedback
from submission.techniques import blank_techniques
from submission.board.probes import (CHECK_TIMEOUT_CAP_S, check_timeout_s, dump_check,
                                     read_board)
from submission.board.text import (base_region, drop_declaration, withdraw, withdraw_only)
from submission.board.types import (Board, Goal, all_cell_spans, author_free,
                                    carry_goals, carry_messages, inherit,
                                    reparent_target)
from submission.run.budget import Budget
from submission.run.context import Run
from submission.run.delivery import Delivery


# Live branches: alternative proof files racing on the same problem. A second
# accepted answer to a goal one model already moved becomes a sibling branch
# rather than a stale reply. Measured on p09: the run was decided by one such
# choice at t=50s, and there was no way to hedge it.
BEAM = 2
# A board that has accepted nothing for this share of the window is stuck
# whatever its counts say. Measured on p09 (reg61b): 7 of 30 steps accepted,
# both withdrawals on one route, and the clock ran out before the counts did.
STALL_SHARE = 0.12
# A goal inside a `have ... := by` that has been rejected this many times takes
# the `have` down with it, and everything after it in its block: the board goes
# back to before the decomposition. Measured on rmo_2000_2: a false `have`
# posted at t=64 made every later goal a contradiction and the lemma unprovable.
WITHDRAW_AFTER = 4
# A goal this many rejections deep is still open, only last in line. Time and
# money are the exits; a goal is never declared hopeless by count alone.
LAST_IN_LINE = 6


class Blackboard:
    def __init__(self, run: Run, budget: Budget, delivery: Delivery) -> None:
        self.run, self.budget, self.delivery = run, budget, delivery
        self.board = Board(run.text)
        self.branches: list[Board] = []
        self.sound: dict[int, str] = {}
        self.changed = asyncio.Event()
        self.progress_at = budget.started
        # Statement -> the block that closed a cell stating it. A closed cell is
        # a proof of a theorem; withdrawing what enclosed it does not unprove
        # it (measured on rmo_2001_2: the final goal, closed at 67 s, came back
        # as new after the enclosing have was withdrawn and was never reclosed).
        self.proven: dict[str, str] = {}
        self.withdrawn: dict[str, list[str]] = {}
        self.undone: dict[str, list[str]] = {}
        self.dissolved = 0
        self.next_bid = 1
        self.lenient = False

    @contextlib.contextmanager
    def lenient_checks(self):
        """While this is open a check may take the cap timeout and a slow step
        is not held against its author. For work whose cost is paid once: a
        leaf block, or a step that closes its goal."""
        self.lenient = True
        try:
            yield
        finally:
            self.lenient = False

    def focus(self, b: Board) -> None:
        self.board = b

    def live(self, bid: int) -> Board | None:
        return next((b for b in self.branches if b.bid == bid), None)

    def fork(self, base: Board) -> Board | None:
        """A sibling branch from `base`, made current, or None if the beam is
        full. Every branch bid comes from here, so no two can collide."""
        if len(self.branches) >= BEAM + 1:
            return None
        fresh = Board(base.text, list(base.goals), list(base.messages),
                      base.accepted, self.next_bid)
        self.next_bid += 1
        self.sound[fresh.bid] = self.sound.get(base.bid, base.text)
        self.branches.append(fresh)
        self.focus(fresh)
        return fresh

    def discard(self, bid: int) -> None:
        """Drop a branch that went nowhere. Branches enter in `fork` and in
        `commit`, and leave here or in `prune`: four sites, not two."""
        gone = self.live(bid)
        if gone is not None:
            self.branches.remove(gone)

    def prune(self) -> None:
        while len(self.branches) > BEAM:
            worst = max(self.branches, key=lambda b: b.score)
            self.branches.remove(worst)
            self.run.events.append({"stage": "prune", "bid": worst.bid, "goals": len(worst.goals)})

    async def look(self, candidate: str, base: Board | None = None,
                   focus: int | str | None = None, edited: Goal | None = None) -> Board:
        """The board after one Lean check: the whole file as cells, or, with
        a focus, that one cell (or proof) checked and the rest inherited."""

        old = base_region(base, focus, edited) if base is not None and focus is not None else None
        if focus is not None and old is None:
            focus = None
        rendered = render_check(candidate, self.run.cells, focus)
        timeout_s = CHECK_TIMEOUT_CAP_S if self.lenient else check_timeout_s((base or self.board).ms)
        check = await self.run.services.lean.check_file(blank_techniques(rendered.text), timeout_s=timeout_s)
        messages = remap(check.messages, rendered.lines)
        errors = [m for m in messages if isinstance(m, dict) and m.get("severity") == "error"]
        dump_check(rendered.text, focus, check)
        for m in check.messages:
            if m.get("severity") == "error" and str(m.get("data", "")).startswith("unexpected"):
                at = message_line(m) or 0
                shown = rendered.text.split("\n")
                self.run.events.append({"stage": "render_fault", "said": str(m.get("data"))[:80],
                               "lines": shown[max(at - 2, 0):at + 1]})
                break
        if focus is None:
            # An error on a marker line is the cell's own header or its link
            # failing, not the proof: that cell goes back inline.
            at = {message_line(m) for m in errors}
            broken = [sp for sp in all_cell_spans(candidate) if sp.start in at]
            if broken and self.dissolved < 8:
                self.dissolved += len(broken)
                text = candidate
                for sp in broken:
                    self.run.events.append({"stage": "inline", "cell": sp.id, "why": "link"})
                    text = dissolve(text, sp.id)
                return await self.look(text, base)
        # As the kit's: no error, no `sorry` anywhere (a `sorry` inside a line is
        # no placeholder, and the grader rejects sorryAx; measured on p10: a
        # board with none open delivered a file the comparator refused).
        accepted = not check.timed_out and not errors and not re.search(r"\bsorry\b", candidate)
        found = read_board(candidate, messages, accepted)
        found.ms = check.duration_ms
        if rendered.region is not None and base is not None and old is not None:
            new = rendered.region
            # Measured on rmo_2000_6: without the reparent the stale-report
            # filter let `case refine_1.refine_2` vanish and the board was
            # delivered with a sorry.
            parent = reparent_target(candidate, new, focus, found.goals, errors)
            if parent is not None:
                return await self.look(candidate, base, parent, edited)
            shown = rendered.text.split("\n")
            probed = {rendered.lines[i] for i, l in enumerate(shown) if CELL_PROBE in l}
            nested_old = {sp.id for sp in all_cell_spans(base.text)} - ({focus} if isinstance(focus, int) else set())
            goals = carry_goals(base.goals, found.goals, probed, old, nested_old)
            if goals is None:
                return await self.look(candidate, base)
            kept = carry_messages(base.messages, base.goals, goals, probed, old,
                                  (new[1] - new[0]) - (old[1] - old[0]),
                                  edited.line if edited is not None else old[0], nested_old)
            found = Board(candidate, goals, kept + messages, accepted, base.bid, check.duration_ms)
        for g in found.goals:
            if g.stmt:
                self.run.notes[g.key].known_stmt = g.stmt
        found.goals = [g if g.stmt or not self.run.notes[g.key].known_stmt else
                       Goal(g.line, g.indent, g.decl, g.text, self.run.notes[g.key].known_stmt, g.cell)
                       for g in found.goals]
        return found

    def remember_closed(self, b: Board) -> None:
        lines = b.text.split("\n")
        for sp in all_cell_spans(b.text):
            stmt = self.run.cells.statements.get(sp.id)
            if not stmt or stmt in self.proven or any(sp.holds(g.line) for g in b.goals):
                continue
            body = [l[sp.indent:] if len(l) - len(l.lstrip()) >= sp.indent else l.lstrip()
                    for l in lines[sp.start:sp.end]]
            block = strip_markers("\n".join(body))
            if block.strip() and "sorry" not in block:
                self.proven[stmt] = block
                self.run.events.append({"stage": "proven", "cell": sp.id, "stmt": stmt[-80:], "lines": block.count("\n") + 1})

    async def settle(self, candidate: Board) -> Board:
        """A placeholder with no goal is dropped; a goal with no placeholder
        gets one; several goals behind one placeholder each get their own."""

        for _ in range(4):
            _, spare, dear, broken = classify(candidate.messages)
            surplus = [l for l in (message_line(m) for m in spare) if l]
            idle = [g.line for g in candidate.goals if not g.text]
            if surplus or (idle and not dear and not broken):
                candidate = await self.look(drop_lines(candidate.text, surplus or idle))
                continue
            for goal in candidate.goals:
                if goal.text.count("⊢") >= 2 and not self.run.notes[goal.key].divided:
                    self.run.notes[goal.key].divided = True
                    apart = split_cursor(candidate.text, goal.text, candidate.index(goal))
                    if apart:
                        self.run.events.append({"stage": "split", "goals": goal.text.count("⊢")})
                        candidate = await self.look(apart)
                        break
            else:
                return candidate
        return candidate

    async def commit(self, candidate: Board, progress: bool = True) -> None:
        """Make a board current, after its own housekeeping. Every commit
        but a restart or a withdrawal is progress for the stall clock."""
        if progress:
            self.progress_at = time.monotonic()
        bid = self.board.bid
        fresh = await self.settle(candidate)
        fresh.bid = bid
        inherit(self.board.goals, fresh.goals, self.run.notes)
        _, _, dear, broken = classify(fresh.messages)
        if broken or dear:
            if fresh.text != self.sound.get(bid, ""):
                self.run.events.append({"stage": "repair", "bid": bid,
                               "why": "cost" if dear and not broken else "error",
                               "said": format_messages(broken or dear)[:300]})
                fresh = await self.look(self.sound.get(bid, self.run.text))
                fresh.bid = bid
        else:
            self.sound[bid] = fresh.text
            self.remember_closed(fresh)
        self.board = fresh
        for i, b in enumerate(self.branches):
            if b.bid == bid:
                self.branches[i] = fresh
                break
        else:
            self.branches.append(fresh)
        finished_text = self.delivery.done_text(self.board)
        self.delivery.offer(finished_text or self.board.text, finished_text is not None)
        self.changed.set()
        self.changed.clear()

    async def take_back(self, author: str, goal: Goal, why: str = "") -> bool:
        """The `have` this goal is the body of comes off the board, with the
        rest of its block; the goal it was posted on is told why. True when
        the board changed."""
        why = why or f"after {WITHDRAW_AFTER} failed attempts to prove it"

        fresh, statement = withdraw_only(self.board.text, goal)
        if not fresh and goal.decl and goal.decl not in self.run.graded:
            # A hoisted lemma has no enclosing have; it goes as a whole when
            # its goal keeps failing, if the file still stands without it.
            # Measured on rmo_2000_6: rmo_2000_6_part1 : IsLeast S 20 (false,
            # undecidable for the audit) sat on the board with nothing to take it back.
            span = proof_span(self.board.text, goal.decl)
            head = DECL_HEAD.match(self.board.text[span[0]:span[1]]) if span else None
            dropped = drop_declaration(self.board.text, goal.decl)
            trimmed = await self.look(dropped)
            if head and not classify(trimmed.messages).failures:
                statement = head.group(1).strip()
                self.run.events.append({"kind": "withdraw", "by": author, "decl": goal.decl,
                               "have": statement[:120], "tries": self.run.notes[goal.key].tries})
                for g in self.run.graded:
                    self.withdrawn.setdefault(g, []).append(statement)
                await self.commit(trimmed, progress=False)
                return True
            return False
        if not fresh:
            return False
        # Only the have goes; if Lean then finds the rest of the block broken
        # (it used the name), the rest goes too. Measured on rmo_2000_6:
        # withdrawing h_witness took h_min, the whole crux, which never used it.
        trimmed = await self.look(fresh)
        whole = False
        if classify(trimmed.messages).failures:
            fresh, statement = withdraw(self.board.text, goal)
            trimmed, whole = await self.look(fresh), True
        self.run.events.append({"kind": "withdraw", "by": author, "have": statement[:120],
                       "tries": self.run.notes[goal.key].tries, "whole_block": whole})
        self.withdrawn.setdefault(goal.decl, []).append(statement)
        await self.commit(trimmed, progress=False)
        back = next((g for g in reversed(self.board.goals) if g.decl == goal.decl
                     and g.line <= goal.line), None)
        if back is not None:
            self.run.notes[back.key].said = Feedback(
                author, f"`{statement}` was posted here as a `have` and withdrawn "
                f"{why}. The board is "
                "back to before it. Do not restate that fact; prove this goal "
                "another way, or through facts that are easier to prove", "withdrawn")
        return True

    def exhausted(self) -> bool:
        """Every open goal answered with a repeat by every model: nothing
        more will come from asking, so the board has to change."""
        return bool(self.board.goals) and not self.run.notes.busy() and all(
            all(m in self.run.notes[g.key].repeated for m in self.run.cfg.lines) for g in self.board.goals)

    def all_last_in_line(self) -> bool:
        return bool(self.board.goals) and not self.run.notes.busy() and all(
            self.run.notes[g.key].tries >= LAST_IN_LINE for g in self.board.goals)

    def stalled(self) -> bool:
        """Nothing accepted for STALL_SHARE of the window, no worker mid-step."""
        return bool(self.board.goals) and not self.run.notes.busy() and (
            time.monotonic() - self.progress_at > STALL_SHARE * self.run.cfg.time_limit_s)

    def pick(self, model: str) -> tuple[Board, Goal] | None:
        """The best branch's least-tried unclaimed goal; with none unclaimed
        anywhere, one the other model holds, so a 158s reply does not idle
        the fast model. Measured on p09: 4 minutes of 20 went that way."""

        # A branch the other model is working on comes after the ones it is
        # not: with two routes open both workers went to the better-ranked
        # one and the other route got 2 turns in 40 (measured on rmo_2000_6).
        busy = {b.bid for b in self.branches for g in b.goals
                if self.run.notes[g.key].claimed_by not in (None, model)}
        options = []
        for rank, b in enumerate(sorted(self.branches, key=lambda b: b.score)):
            for g in b.goals:
                # A goal this model has already answered with a byte-identical
                # rejected block is not offered to it again until the board
                # changes (measured on rmo_2000_6: 1190 repeats in one run,
                # runs of 125 while the other model was in a long call).
                if g.text and self.run.notes[g.key].claimed_by != model and author_free(self.run.notes[g.key], model):
                    options.append((self.run.notes[g.key].claimed_by is not None,
                                    b.bid in busy and len(self.branches) > 1, rank,
                                    self.run.notes[g.key].tries >= LAST_IN_LINE,
                                    self.run.notes[g.key].tries, g.line, b, g))
        if not options:
            return None
        first = min(options, key=lambda o: o[:6])
        return first[6], first[7]
