"""The cheap things tried before a model is asked.

Each rung answers one shape of goal without spending a token: a cocktail of
tactics, a leaf block, a witness, a generalisation, a library search. `turn`
runs them behind three gates, not one gate each, so a goal gets one round of
them rather than one round per rung. `unstick` is the rung of last resort:
it takes an edit back and reopens what it closed."""

from __future__ import annotations
import re
import time

from submission.agent import FEEDBACK_CHARS, format_messages
from submission.cells import enclosing, reset_cell
from submission.conjecture import (families, fits, lemma_text, read_table, table_file,
                                   verified, verify_file)
from submission.framework import (classify, insert_preamble, proof_span, reindent,
                                  restate, root_names)
from submission.framework_agent import Feedback
from submission.leaves import _hyps as leaf_hyps, _sum_variables, leaf_candidates
from submission.techniques import blank_techniques
from submission.board.probes import (UNKNOWN_NAME_QUOTED, WITNESS_BOUND, apply_file, check_timeout_s,
                                     existential, fired_closer, read_suggestions,
                                     read_witnesses, tagged_closers, witness_search_file)
from submission.board.reply import claim_of
from submission.board.text import (context_grows, enclosing_chain, put, settled_inside,
                                   split_facts, stated_facts, withdraw_only)
from submission.board.types import (Board, Goal, HAVE_HEAD, hypotheses, is_root_goal,
                                    split_top, target_of)
from submission.run.asking import TIMED_OUT, Asking
from submission.run.blackboard import Blackboard
from submission.run.budget import Budget
from submission.run.context import Run


class Ladder:
    def __init__(self, run: Run, budget: Budget, bb: Blackboard, asking: Asking) -> None:
        self.run, self.budget, self.bb, self.asking = run, budget, bb, asking
        self.conjectured: dict[tuple[str, str], str] = {}
        self.cocktail: tuple[str, ...] = ()

    async def sweep(self, goal: Goal) -> bool:
        """The free closers, once per goal. (`exact?` used to follow: measured
        1 of 51 goals closed over 24 runs, and a slow one restarts the container.)"""

        base = self.bb.board
        block = tagged_closers(self.cocktail)
        t0 = time.monotonic()
        nxt, _ = await self.asking.judge(base, goal, block)
        self.run.events.append({"kind": "closers", "by": "harness", "accepted": nxt is not None,
                       "ms": int((time.monotonic() - t0) * 1000)})
        if nxt is None:
            return False
        tactic = fired_closer(nxt.messages, self.asking.last_span, self.cocktail)
        flat = None
        if tactic:
            cell_id = self.run.cells.new(goal.stmt) if goal.stmt and not is_root_goal(base.text, goal) else None
            flat = await self.bb.look(put(base.text, goal, tactic, trailing=False, cell_id=cell_id)[0],
                              base, cell_id if cell_id is not None else (goal.cell or goal.decl), goal)
        if flat is not None and flat.find(goal.key) is None and not any(
                classify(flat.messages)[2:]):
            nxt = flat
        self.run.events.append({"kind": "collapse", "tactic": tactic, "accepted": nxt is flat})
        await self.bb.commit(nxt)
        return True

    async def witness_sweep(self, goal: Goal) -> bool:
        """An existential with a decidable body: Lean enumerates the witnesses
        and the first tuple that closes the goal is written, no model asked.
        Measured on rmo_2000_6: both models guessed `use 10, 1` and `use 2, 4`
        for 12 minutes; the only small witness is a = 1, b = 10."""

        parsed = existential(goal.text)
        if not parsed:
            return False
        names, body = parsed
        imports = self.run.imports
        check = await self.run.services.lean.check_file(witness_search_file(imports, names, body), timeout_s=60)
        found = read_witnesses(check.messages)
        accepted = False
        for row in found:
            for closer in ("norm_num", "decide"):
                block = f"exact ⟨{', '.join(row)}, by {closer}⟩"
                nxt, _ = await self.asking.judge(self.bb.board, goal, block)
                if nxt is not None:
                    await self.bb.commit(nxt)
                    accepted = True
                    break
            if accepted:
                break
        if found:
            # Kept even when the goal closed: the same goal on a sibling
            # branch is not swept again (same key) and reads it from the prompt.
            self.run.notes[goal.key].hint = ("Evaluation over 0 ≤ " + ", ".join(names) + f" < {WITNESS_BOUND} found "
                               "these values satisfy the body: " + "; ".join(
                                   ", ".join(f"{n} = {v}" for n, v in zip(names, row)) for row in found)
                               + (f". `{block}` closed it." if accepted else ""))
        self.run.events.append({"kind": "witnesses", "goal": goal.text[-160:], "found": found,
                       "accepted": accepted, "ms": check.duration_ms})
        return accepted

    async def leaf_sweep(self, goal: Goal) -> bool:
        """Tactic blocks built from the goal's shape (leaves.py), each one
        check, no model asked. Measured on 3 September: three of the four
        unsolved problems were lost on leaves of these shapes after the
        models had found the route."""

        base = self.bb.board
        candidates = leaf_candidates(goal.text) if self.run.cfg.leaves else []
        if not candidates or not self.budget.affordable("leaf"):
            return False
        t0 = time.monotonic()
        tried = 0
        self.budget.heavy_leaf = True
        try:
            for block in candidates:
                tried += 1
                nxt, why = await self.asking.judge(base, goal, block)
                if nxt is not None:
                    self.run.events.append({"kind": "leaf", "goal": goal.text[-120:],
                                   "block": block.split("\n")[-1][:80], "accepted": True,
                                   "ms": int((time.monotonic() - t0) * 1000)})
                    await self.bb.commit(nxt)
                    return True
                if why == TIMED_OUT or not self.budget.affordable("leaf"):
                    break
            self.run.events.append({"kind": "leaf", "goal": goal.text[-120:], "accepted": False,
                           "tried": tried, "ms": int((time.monotonic() - t0) * 1000)})
            return False
        finally:
            self.budget.heavy_leaf = False
            self.budget.spent("leaf", time.monotonic() - t0)

    async def library_sweep(self, goal: Goal, force: bool = False) -> bool:
        """Mathlib asked what unifies with the goal (`apply?`), after the
        closers failed. An `exact` answer is written, no model asked; the
        rest go into the prompt as the names that fit. Measured in the
        image: 4 of 4 leaf goals closed by exact, about 8 s each."""

        if not force and not self.budget.affordable("scan"):
            return False
        # The file's own check time plus the heartbeat-capped search.
        answered, took = await self.asking.probe(apply_file(self.bb.board.text, goal), goal.line, check_timeout_s(self.bb.board.ms) + 30)
        self.budget.spent("scan", took / 1000)
        found = read_suggestions(answered, goal.line)
        accepted = False
        for how, term in found:
            if how != "exact":
                continue
            nxt, _ = await self.asking.judge(self.bb.board, goal, f"exact {term}")
            if nxt is not None:
                await self.bb.commit(nxt)
                accepted = True
                break
        if found and not accepted:
            self.run.notes[goal.key].hint = ("Mathlib's `apply?` on this goal suggested: " + "; ".join(
                f"`{how} {term}`" for how, term in found[:3]) + ". Those unify with the goal; the ?_ holes are what is left to prove.")
        self.run.events.append({"kind": "library", "goal": goal.text[-120:], "found": len(found),
                       "accepted": accepted, "ms": took})
        return accepted

    async def generalise_sweep(self, goal: Goal) -> bool:
        """A sum identity in one variable that its own induction did not
        close: the variable's other occurrences are generalised, each family
        tabulated in Lean and fitted to a shape, a fit that holds below
        VERIFY is posted as a lemma (the induction leaf proves it) and the
        goal rewrites by it. Measured: putnam_2020_a2, 0/32 model proposals."""

        target = target_of(goal.text)
        if goal.decl.startswith("vm_conj_") or "h_gen" in hypotheses(goal.text) or not self.budget.affordable("leaf"):
            return False
        ks = _sum_variables(leaf_hyps(goal.text), target)
        halves = split_top(target, " = ")
        if not ks or halves is None or "=" in halves[0] or "=" in halves[1]:
            return False
        k, lhs = ks[0], halves[0].strip()
        taken = set(hypotheses(goal.text)) | set(re.findall(r"[A-Za-z_][\w']*", target))
        fresh = next((c for c in ("n", "m", "t", "a", "b") if c not in taken), "vm_n")
        fams = families(lhs, k, fresh)
        roots = root_names(self.bb.board.text)
        first = proof_span(self.bb.board.text, roots[0]) if roots else None
        prefix = self.bb.board.text[:first[0]] if first else ""
        found = [(f, g) for (f, g) in self.conjectured if f in fams]
        if not found:
            t0 = time.monotonic()
            for i, fam in enumerate(fams[:6]):
                check = await self.run.services.lean.check_file(
                    blank_techniques(table_file(prefix, fam, fresh, k, i)), timeout_s=60)
                table = read_table(check.messages)
                if not table:
                    continue
                for guess in fits(table, fresh, k, fam)[:2]:
                    check = await self.run.services.lean.check_file(
                        blank_techniques(verify_file(prefix, fam, guess, fresh, k)), timeout_s=60)
                    if verified(check.messages):
                        found.append((fam, guess))
            self.budget.spent("leaf", time.monotonic() - t0)
            self.run.events.append({"stage": "conjecture", "goal": target[:100], "families": len(fams),
                           "fits": [g for _, g in found][:3]})
        if not found:
            return False
        fam, guess = found[0]
        name = self.conjectured.setdefault((fam, guess), f"vm_conj_{len(self.conjectured) + 1}")
        text = self.bb.board.text
        if name not in root_names(text):
            text = insert_preamble(text, lemma_text(name, fresh, k, fam, guess))
        staged = await self.bb.look(text) if text != self.bb.board.text else self.bb.board
        moved = staged.find(goal.key)
        if moved is None or classify(staged.messages)[3]:
            return False
        sub = lambda t: re.sub(rf"(?<![\w'.]){fresh}(?![\w'])", k, t)
        # `k + k` reads as `2 * k` (the form Mathlib's lemmas are stated in).
        spec = re.sub(rf"(?<![\w'.]){k} \+ {k}(?![\w'])", f"2 * {k}", sub(guess))
        facts = [f"have h_gen : {sub(fam)} = {spec} := by simpa only [← two_mul] using {name} {k} {k}"] \
            if spec != sub(guess) else []
        facts.append(f"have h_gen : {sub(fam)} = {sub(guess)} := {name} {k} {k}")
        nxt = None
        for fact in facts:
            nxt, _ = await self.asking.judge(staged, moved, f"{fact}\nrw [h_gen]")
            if nxt is None:
                nxt, _ = await self.asking.judge(staged, moved, fact)
            if nxt is not None:
                break
        self.run.events.append({"stage": "generalise", "lemma": name, "guess": guess,
                       "rewritten": nxt is not None})
        await self.bb.commit(nxt if nxt is not None else staged)
        left = next((g for g in self.bb.board.goals if g.decl == goal.decl and "h_gen" in hypotheses(g.text)), None)
        if left is not None and not self.run.notes[left.key].searched:
            # Mathlib may state the rewritten goal outright (Nat.sum_range_choose_halfway).
            self.run.notes[left.key].searched = True
            await self.library_sweep(left, force=True)
        return True

    async def lift_and_advance(self, base: Board, goal: Goal, block: str,
                               author: str) -> tuple[Board | None, str]:
        """A fact posted with `sorry` inside a `have` goes above the outermost
        `have`: facts live at the shallowest scope. Measured on rmo_2000_2:
        skeletons nested 7 deep, 25 open goals, withdraw never firing."""

        lines = base.text.split("\n")
        chain = enclosing_chain(lines, goal)
        facts, rest = split_facts(block)
        if not chain or not facts:
            return await self.asking.advance(base, goal, block, author)
        known = stated_facts(base.text, goal.decl)
        fresh, dup = [], []
        for f in facts:
            head = HAVE_HEAD.match(f.split("\n")[0])
            claim = " ".join(claim_of(head.group(2).strip()).split())
            (dup if claim in known else fresh).append((f, known.get(claim)))
        if dup and not fresh and not rest:
            names = ", ".join(f"`{n}`" for _, n in dup)
            return None, (f"every fact in that step is already on the board ({names}); "
                          "prove this goal from those facts, or close it directly")
        # Outermost first; a target where Lean does not know one of the
        # goal's own names is too far out, and the next `have` in is tried.
        # Measured on rmo_2000_6: the crux sat under `have h_minimal : ∀ n, ...
        # := by intro n h; rcases h with ⟨a, b, ...⟩`, and every fact about
        # a and b was lifted to where they do not exist.
        local = set(hypotheses(goal.text))
        nxt, why, depth, head = None, "", 0, None
        for depth in range(len(chain), 0, -1):
            outer, head = chain[depth - 1]
            if context_grows(lines, chain, depth, goal):
                continue
            lifted = [reindent(f, head.group(1)) for f, _ in fresh]
            text = "\n".join(lines[:outer] + lifted + lines[outer:])
            shift = sum(f.count("\n") + 1 for f in lifted)
            moved = Goal(goal.line + shift, goal.indent, goal.decl, goal.text, goal.stmt, goal.cell)
            staged = Board(text, base.goals, base.messages, base.accepted, base.bid, base.ms)
            if rest:
                nxt, why = await self.asking.advance(staged, moved, rest, author)
            else:
                nxt, why = await self.bb.look(text, base), ""
                if classify(nxt.messages)[3]:
                    nxt, why = None, format_messages(classify(nxt.messages)[3])[:FEEDBACK_CHARS]
                elif nxt is not None:
                    bad = await self.asking.audit(author, base, nxt)
                    if bad:
                        nxt, why = None, bad
            if nxt is not None or not any(n in local for n in UNKNOWN_NAME_QUOTED.findall(why)):
                break
        else:
            depth = 0
        if nxt is None and depth == 0:
            return await self.asking.advance(base, goal, block, author)
        if nxt is None:
            return None, (why + f"\n(a fact stated inside `{head.group(2).strip()[:60]}` "
                          "is posted before that `have`, at the top of the proof; it can "
                          "only use the theorem's variables and the facts above it)")
        self.run.events.append({"kind": "lifted", "by": author, "facts": len(lifted),
                       "dup": len(dup), "from_depth": len(chain), "to_depth": depth})
        if dup:
            self.run.notes[goal.key].said = Feedback(author, "already on the board: " + ", ".join(
                f"`{n}`" for _, n in dup), "lifted")
        return nxt, ""

    async def unstick(self) -> None:
        """Every goal last in line, or nothing accepted for a while: the
        innermost open have comes off on a fork, else the worst goal's
        declaration starts over and what was said and planned for it goes.
        Time and money bound how often; a count did not, and this was
        unreachable until v7.40."""


        worst = max(self.bb.board.goals, key=lambda g: self.run.notes[g.key].tries, default=None)
        if worst is None or not worst.decl:
            return
        # Measured on rmo_2000_6 (one55a 08:46→08:51): one goal left, 6 tries,
        # and the declaration went back to its statement. Goals sitting among
        # proved facts restart themselves once before the declaration does.
        leaves = [g for g in self.bb.board.goals if not self.run.notes[g.key].leaf_restarted
                  and settled_inside(self.bb.board.text, g) >= 2]
        if leaves:
            for g in leaves:
                self.run.notes[g.key].leaf_restarted = True
                self.run.notes.forget(g.key)
            self.run.events.append({"kind": "leaf_restart", "by": "harness", "goals": len(leaves),
                           "settled": settled_inside(self.bb.board.text, leaves[0])})
            return
        # The innermost open `have` goes first and its siblings stay: undo at
        # the goal, not the declaration. The declaration restarts only when
        # no open goal sits inside a `have` any more.
        inside = [g for g in self.bb.board.goals if withdraw_only(self.bb.board.text, g)[0]]
        if inside:
            deepest = max(inside, key=lambda g: (len(g.indent), self.run.notes[g.key].tries))
            # The stuck subtree is not thrown away: the board with it stays
            # as a sibling branch and the take-back happens on a fork, so
            # the two ways forward race, as two plans do.
            fork = self.bb.fork(self.bb.board)
            if fork is not None:
                self.run.events.append({"stage": "fork", "why": "stall",
                                        "from": self.bb.branches[0].bid, "to": fork.bid})
            if await self.bb.take_back("harness", deepest,
                               "after the board made no progress for a while"):
                self.bb.prune()
                return
        # A goal inside a cell: that cell alone goes back to its `sorry`
        # (its block was one step's answer), the rest of the proof stays.
        held = enclosing(self.bb.board.text, worst.line)
        if held is not None:
            fork = self.bb.fork(self.bb.board)
            if fork is not None:
                self.run.events.append({"stage": "fork", "why": "reset",
                                        "from": self.bb.branches[0].bid, "to": fork.bid})
            self.run.events.append({"stage": "reset", "cell": held.id, "decl": worst.decl,
                           "tries": self.run.notes[worst.key].tries})
            self.run.notes.forget(worst.key)
            first_line = self.bb.board.text.split("\n")[held.start].strip()
            self.bb.undone.setdefault(worst.decl, []).append(first_line)
            await self.bb.commit(await self.bb.look(reset_cell(self.bb.board.text, held)), progress=False)
            self.bb.prune()
            return
        fresh_text, _ = restate(self.bb.board.text, worst.decl)
        self.run.events.append({"stage": "restate", "decl": worst.decl,
                       "tries": self.run.notes[worst.key].tries})
        self.run.notes.forget_decl(worst.decl)
        await self.bb.commit(await self.bb.look(fresh_text), progress=False)
