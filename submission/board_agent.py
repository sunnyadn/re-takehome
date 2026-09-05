"""A board of open goals, each known by its content, two models working two
of them at once; Lean judges every edit against the whole file. The file is
still the proof; a reply is read once, as a proof of whatever it names."""


from __future__ import annotations

import asyncio
import re
import time
from typing import Any, Sequence

from re_harness import AgentResult, LLMCallError, Problem, Services
from re_harness.budget import BudgetAccountingError, BudgetExceeded
from re_harness.lean import LeanRuntimeError

from submission.cells import (CELL_PROBE, Cells, dissolve, enclosing, modular, remap, render_check, reopen_past_cell, reset_cell, strip_markers)
from submission.conjecture import (families, fits, lemma_text, read_table, table_file,
                                   verified, verify_file)
from submission.leaves import _hyps as leaf_hyps, _sum_variables, leaf_candidates
from submission.sampling import read_sample_hit, sample_file, sampled_search
from submission.techniques import (PREAMBLE_MARK, blank_techniques, strip_techniques,
                                   uses_techniques, without_techniques)
from submission.agent import (BUDGET_HEADROOM, technique_card, with_preamble, FEEDBACK_CHARS, Ledger, in_file_coordinates, answer_names, declared_names, format_messages, grade, normalise_imports, scoring_faults, split_files, sweep_files, usable_cocktail)
from submission.framework import (DECL_HEAD, axiom_probe, classify, definition_slots, fill_definition, drop_lines, graded_theorems, hand_to_search, in_span, insert_above, insert_preamble, is_done, line_of, message_line, message_span, placeholders, prefixes, proof_span, reindent, render, restate, root_names, split_cursor, unreachable)
from submission.framework_agent import (VACUOUS, BUDGET_RETRY, FILE_CHARS, ANSWER_TOKENS, strip_fences, GOAL_CHARS, LOOSE_DRAIN_S, RAISED_BUDGETS, SLOW_COMPILE_MS, FRAMEWORK_SYSTEM, Feedback, FrameworkAgent, State, notes_for, sheet_for)
from submission.board.types import (Board, Edit, Goal, HAVE_HEAD, Notes, all_cell_spans, author_free, binder_names, hyp_count, hypotheses, inherit, is_root_goal, narrates, owner, shift_message, signature, split_top, step_tokens, target_of)
from submission.board.reply import (ascribe_literals, claim_of, dialect, interpret, mine_statements, salvage, set_elements, unwrap)
from submission.run.budget import Budget
from submission.run.context import Run
from submission.run.delivery import Delivery
from submission.run.blackboard import BEAM, WITHDRAW_AFTER, Blackboard
from submission.run.asking import AUDIT_SYSTEM, AUDIT_TOKENS, TIMED_OUT, Asking
from submission.run.ladder import Ladder
from submission.board.text import (base_region, context_grows, drop_declaration, enclosing_chain, enclosing_have, inflated, is_stated, proved_facts, put, restates, settled_inside, shed_unreferenced, split_facts, split_statement, stated_facts, view, withdraw, withdraw_only)
from submission.board.probes import (CHECK_TIMEOUT_CAP_S, CHECK_TIMEOUT_FLOOR_S, PROBE, UNKNOWN_NAME, WITNESS_BOUND, apply_file, audit_prompt, check_timeout_s, container_memory_bytes, counterexample_search, dump_check, existential, extract_file, fired_closer, goal_tokens, have_extract_file, is_closed, library_file, library_names, name_probe_file, read_board, read_library, read_name_probe, read_suggestions, read_witness, read_witnesses, render_all, searched_clean, statements, tagged_closers, witness_file, witness_search_file)

# The cursor loop's prompt, less "give every have a body": on the board a
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
# When every goal is last in line, the declaration holding the worst of them
# goes back to its statement, with its goals' history cleared. Time and money
# bound how often; a count did not, and the branch was unreachable until v7.40.
# A worker with no goal to take waits this long for the board to change.
IDLE_WAIT_S = 2.0




# The REPL keeps every command's state. Measured in the harness image: a real
# board leaves 46–77 MB behind per check (a trivial file leaves nothing), the
# container's cap is 5 GiB, so the kernel killed the REPL every 55–90 checks,
# mid-check, and the next check paid a cold Mathlib import (28 kills in three
# hours across the lanes on one machine). Renewed on our terms instead: when
# its memory is up (sampled) or, without a reading, after this many checks,
# while a model reply is awaited so the import overlaps that wait. Measured on
# p10 (win): 787 MB at check 9, 2980 MB at check 16 on one theorem; with
# cells a check retains almost nothing (682 MB after import, +2 MB per small
# check), and one `exact?` takes the container to 2.7 GB for good (its index),
# which a renew only makes it load again (27 s). So the threshold sits near
# the 5 GB limit and the count is a backstop.
# Measured again with cells (p10, win): at 3.1-3.4 GB a check of three bare
# probes took 118 s and `intro n hn` 108 s (the container thrashing), so the
# threshold sits below that and above one search's residue (2.7 GB).
RENEW_AT_BYTES = int(3.0 * 2 ** 30)
RENEW_AFTER_CHECKS = 200
MEMORY_SAMPLE_EVERY = 4




class RenewingLean:
    """Counts the checks on the current Lean container, samples its memory,
    and renews it on request; check results pass through unchanged."""

    def __init__(self, inner: Any, events: list[dict[str, Any]]) -> None:
        self._inner = inner
        self._events = events
        self.checks = 0
        self.memory: int | None = None
        self.task: asyncio.Task[Any] | None = None
        self._sampling: asyncio.Task[Any] | None = None

    def __getattr__(self, name: str) -> Any:
        return getattr(self._inner, name)

    async def check_file(self, source: str, timeout_s: Any = None) -> Any:
        if self.task is not None and not self.task.done():
            await asyncio.gather(self.task, return_exceptions=True)
        check = await self._inner.check_file(source, timeout_s=timeout_s)
        self.checks = 1 if getattr(check, "container_restarted", False) else self.checks + 1
        name = getattr(self._inner, "_container_name", None)
        if name and self.checks % MEMORY_SAMPLE_EVERY == 0 and (self._sampling is None or self._sampling.done()):
            self._sampling = asyncio.ensure_future(self._sample(name))
        return check

    async def _sample(self, name: str) -> None:
        self.memory = await asyncio.to_thread(container_memory_bytes, name)
        self._events.append({"stage": "memory", "checks": self.checks,
                             "mb": None if self.memory is None else self.memory // 2 ** 20})

    def due(self) -> bool:
        if self.task is not None and not self.task.done():
            return False
        if self.memory is not None:
            return self.memory >= RENEW_AT_BYTES
        return self.checks >= RENEW_AFTER_CHECKS

    def renew(self) -> None:
        """Start the renewal in the background; every check waits for it."""
        if not (hasattr(self._inner, "close") and hasattr(self._inner, "start")):
            return
        checks, memory = self.checks, self.memory
        self.checks, self.memory = 0, None

        def swap() -> None:
            self._inner.close()
            self._inner.start()

        async def run() -> None:
            t0 = time.monotonic()
            await asyncio.to_thread(swap)
            self._events.append({"stage": "renew", "checks": checks,
                                 "mem_mb": (memory or 0) // 2 ** 20 or None,
                                 "ms": int((time.monotonic() - t0) * 1000)})
        self.task = asyncio.ensure_future(run())


















# There is no refutation probe. Proving `¬ target` from the context by
# decide/omega only refutes the goal when the context is consistent, and a
# proof by contradiction lives in an inconsistent one: on p09 the probe
# "refuted" six true goals (`h1 : n % 3 = 1 ... ⊢ False`) and undid the proof.



































































TUPLE_IN = re.compile(r"[⟨(]\s*([A-Za-z_][\w']*(?:\s*,\s*[A-Za-z_][\w']*)+)\s*[⟩)]\s*∈")


































































































class BoardAgent(FrameworkAgent):
    """The cursor loop's primitives, driven by a board instead of a cursor."""

    async def _define(self, problem: Problem, text: str, services: Services,
                      ledger: Ledger, events: list[dict[str, Any]]) -> str:
        """The answer term is the first claim of the proof and the one no later
        step can repair, so every model offers one and each offer is audited
        against the theorem's own statement; a broken offer is not used."""

        for name, kind in definition_slots(text):
            offers: list[tuple[str, str]] = []
            note = ""
            for attempt in range(2 * len(self.config.lines)):
                model = self.config.lines[attempt % len(self.config.lines)]
                ask = (f"Give the value of `{name} : {kind}`.\n\nProblem: "
                       f"{problem.description}\n\nFile:\n{text[:FILE_CHARS]}\n\n"
                       f"Reply with one Lean 4 term of type `{kind}` on a single line, "
                       "and nothing else. It is the answer itself, not a proof of it, "
                       "so no tactics and no `by`. A finite set is written as its "
                       "elements, `({(1, 2), (3, 4)} : T)`, never as a set-builder." + note)
                # Measured one23b: with reasoning on, qwen answered the term
                # question with a page of derivation twice; gpt-oss alone offered.
                said, _ = await self._call(model, ask, ANSWER_TOKENS, services, ledger,
                                           think=not narrates(model))
                term = dialect(" ".join(strip_fences(said).split("\n")))[:FEEDBACK_CHARS].strip()
                if not term or term.startswith("by "):
                    note = "\n\nYour last reply was not a term."
                    continue
                candidate = fill_definition(text, name, term)
                check = await services.lean.check_file(candidate)
                if classify(check.messages)[3]:
                    note = ("\n\nThat term did not elaborate. Lean said:\n"
                            + format_messages(check.messages)[:FEEDBACK_CHARS])
                    continue
                note = ""
                if term not in [t for t, _ in offers]:
                    offers.append((term, candidate))
                if len(offers) >= 2 or attempt >= len(self.config.lines) and offers:
                    break
            chosen = None
            for term, candidate in offers:
                # The theorem that states the answer's role is the one audited.
                users = [n for n in root_names(candidate)
                         if (span := proof_span(candidate, n)) and name in candidate[span[0]:span[1]]]
                verdict, values = await self._audit_root(
                    candidate, (users or root_names(candidate))[0], services, ledger, term)
                events.append({"stage": "define", "name": name, "kept": verdict != "refuted",
                               "term": term[:120], "verdict": verdict, "values": values})
                if verdict != "refuted" and chosen is None:
                    chosen = candidate
            if chosen is None and offers:
                chosen = offers[0][1]
            if chosen is not None:
                text = chosen
        return text

    async def _share(self, problem: Problem, text: str, services: Services,
                     ledger: Ledger, events: list[dict[str, Any]]) -> str:
        """As the framework's, and each kept statement is audited: a shared
        lemma that a witness breaks does not enter the file."""

        before = set(root_names(text))
        text = await super()._share(problem, text, services, ledger, events)
        seen: set[str] = {signature(text, n) for n in before}
        for name in [n for n in root_names(text) if n not in before]:
            sig = signature(text, name)
            if sig in seen:
                # Measured on p09: both models proposed the same lemma under two
                # names and both were being proved.
                events.append({"stage": "share-audit", "name": name, "verdict": "duplicate"})
                text = drop_declaration(text, name)
                continue
            seen.add(sig)
            verdict, values = await self._audit_root(text, name, services, ledger)
            events.append({"stage": "share-audit", "name": name, "verdict": verdict,
                           "values": values})
            if verdict == "refuted":
                text = drop_declaration(text, name)
        return text

    async def _enumerated(self, prefix: str, groups: Sequence[str], target: str,
                          services: Services) -> tuple[bool, dict[str, str] | None]:
        """(the walk ran, values that satisfy every hypothesis and break the
        claim) over 0..WITNESS_BOUND-1. A claim the walk covers is settled here
        and no model is asked about it: measured over 7 runs, every refutation
        with ℕ binders came from the walk and the auditor's came from closed
        claims and ℤ, while audit calls were half of all calls (108 of 285 on
        putnam_2020_a2, 1990 s of latency, one reply 482 s under the board lock)."""
        search = counterexample_search(groups, target)
        if not search:
            # A statement over a sequence (x : ℕ → ℝ) with ∀-hypotheses: sampled
            # sequences over ℚ, the ∀s bounded (measured on rmo_2000_3: every
            # claim carries hpos/hmono/hsq and the walk cannot bind a function).
            sampled = sampled_search(groups, target)
            if not sampled:
                return False, None
            names, seq, body = sampled
            check = await services.lean.check_file(sample_file(prefix, names, seq, body), timeout_s=60)
            met, hit = read_sample_hit(check.messages, names)
            return met, hit
        names, body = search
        check = await services.lean.check_file(witness_search_file(prefix, names, body), timeout_s=60)
        rows = read_witnesses(check.messages)
        if rows and len(rows[0]) == len(names):
            return True, dict(zip(names, rows[0]))
        return searched_clean(check.messages), None

    async def _audit_root(self, text: str, decl: str, services: Services,
                          ledger: Ledger, term: str = "") -> tuple[str, dict[str, str]]:
        """A declaration's statement tried against a witness: Lean states its
        goal, each element of an explicit set answer (if `term` is one) and
        then the auditor's values are tried as values that make it fail."""

        roots = root_names(text)
        holes = [(line_of(text, m.start()), m.group(1)) for m in placeholders(text)]
        at = next(((l, ind) for l, ind in holes if owner(text, l) == decl), None)
        if not roots or at is None:
            return "unstated", {}
        goal = Goal(at[0], at[1], decl, "")
        check = await services.lean.check_file(extract_file(text, [goal]),
                                               timeout_s=CHECK_TIMEOUT_FLOOR_S)
        stmt = statements(check.messages).get(goal.line, "")
        parsed = split_statement(stmt) if stmt else None
        if not parsed:
            return "unstated", {}
        groups, target = parsed
        first = proof_span(text, roots[0])
        prefix = text[:first[0]] if first else ""
        names = [n for g in groups for n in binder_names(g)]
        tries: list[dict[str, str]] = []
        tuple_names = TUPLE_IN.search(target)
        elements = set_elements(term)
        if tuple_names and elements:
            keys = [k.strip() for k in tuple_names.group(1).split(",")]
            tries += [dict(zip(keys, e)) for e in elements if len(e) == len(keys)]
        async def breaks(values: dict[str, str]) -> bool:
            probe = await services.lean.check_file(witness_file(prefix, groups, values, target),
                                                   timeout_s=CHECK_TIMEOUT_FLOOR_S)
            return probe.accepted
        for values in tries:
            if await breaks(values):
                return "refuted", values
        searched, found = await self._enumerated(prefix, groups, target, services)
        if found and await breaks(found):
            return "refuted", found
        if searched:
            return "holds", {}
        auditor = next((m for m in self.config.lines if not narrates(m)), self.config.lines[0])
        reply, _ = await self._call(auditor, audit_prompt(stmt, without_techniques(prefix)[0].replace("import Mathlib", "")),
                                    AUDIT_TOKENS, services, ledger, system=AUDIT_SYSTEM)
        given = {n: v for n, v in (read_witness(reply) or {}).items() if n in names}
        if (given or not names) and await breaks(given):
            return "refuted", given
        return ("holds" if tries or given or "holds" in reply else "unverified"), {}

    async def _call(self, model: str, prompt: str, max_tokens: int, services: Services,
                    ledger: Ledger, *args: Any, **kwargs: Any) -> tuple[str, str]:
        lean = getattr(services, "lean", None)
        if isinstance(lean, RenewingLean) and lean.due():
            lean.renew()
        return await super()._call(model, prompt, max_tokens, services, ledger, *args, **kwargs)

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        services = in_file_coordinates(services)
        cfg = self.config
        events: list[dict[str, Any]] = []
        if not isinstance(services.lean, RenewingLean):
            services.lean = RenewingLean(services.lean, events)
        run = Run(problem, services, cfg, events)
        ledger, names, graded = run.ledger, run.names, run.graded
        models, first_graded = run.models, run.first_graded
        text = run.text
        lock = asyncio.Lock()
        notes = run.notes
        budget = Budget(run)
        delivery = Delivery(self, run, budget)
        bb = Blackboard(run, budget, delivery)
        asking = Asking(self, run, budget, bb)
        ladder = Ladder(self, run, budget, bb, asking)

        finished = False













        # Statement → the block that closed a cell stating it. A closed cell is
        # a proof of a theorem; withdrawing what enclosed it does not unprove
        # it (measured on rmo_2001_2: the final goal, closed at 67 s, came back
        # as new after the enclosing have was withdrawn and was never reclosed).









        # The environment's answer to a goal's vocabulary, once per token set.
        # Every plan asked for a declaration, kept across restarts: the next
        # plan is asked to differ from them.
        routes: dict[str, list[str]] = {}
















        async def apply(author: str, goal: Goal, edits: list[Edit]) -> bool:
            """Every edit a reply asked for, each against the board as it stands."""

            took = False
            for edit in edits:
                here = bb.board.find(goal.key)
                if edit.kind == "probe":
                    printed = await self._probe(State(text=bb.board.text), edit.body, services)
                    notes[goal.key].said = Feedback(author, printed, "probe")
                    events.append({"kind": "probe", "by": author, "printed": printed[:80]})
                    continue
                if edit.kind == "drop":
                    events.append({"kind": "drop", "by": author, "name": edit.name})
                    notes[goal.key].said = Feedback(
                        author, f"`{edit.name}` is already declared; work the goal "
                        "you were shown, do not restate it", "rejected")
                    notes[goal.key].tries += 1
                    continue
                if edit.kind == "step":
                    if here is None:
                        events.append({"kind": "stale", "by": author})
                        continue
                    if edit.body in notes[here.key].refused:
                        # Measured on p10: five byte-identical replies in a row.
                        events.append({"kind": "repeat", "by": author})
                        notes[here.key].repeated.add(author)
                        notes[goal.key].said = Feedback(
                            author, "that is byte for byte the step already rejected "
                            "on this goal; Lean will say the same thing. Try a "
                            "different route: " + notes[goal.key].said.text[:600]
                            if notes[goal.key].said else "that step was already rejected here")
                        notes[goal.key].tries += 1
                        continue
                    # Measured on p09: a substring match locked a worker out for 19
                    # min once `n % 3 = 0` was withdrawn and the goal read `⊢ n % 3 = 0`.
                    # Only a `have` stating the claim again is a restatement.
                    if restates(edit.body, bb.withdrawn.get(here.decl, ())):
                        events.append({"kind": "restated", "by": author})
                        notes[goal.key].said = Feedback(author, "that step restates a fact "
                                                  "already withdrawn from this declaration")
                        notes[goal.key].tries += 1
                        continue
                    present = proved_facts(bb.board.text, here)
                    if restates(edit.body, present):
                        # Measured on p09: the same claim proved twice in one declaration.
                        names = [present[c] for c in present if restates(edit.body, [c])]
                        events.append({"kind": "restated", "by": author, "of": names[:3]})
                        notes[goal.key].said = Feedback(author, "that step states a fact already "
                                                  "on the board as " + ", ".join(f"`{n}`" for n in names[:3])
                                                  + "; use it, do not prove it again")
                        notes[goal.key].tries += 1
                        continue
                    nxt, why = await ladder.lift_and_advance(bb.board, here, edit.body, author)
                    if nxt is None:
                        notes[here.key].refused.add(edit.body)
                    events.append({"kind": "step", "by": author, "accepted": nxt is not None,
                                   **({} if nxt is not None else {"why": str(why)[:160]})})
                    if nxt is None:
                        notes[goal.key].said = Feedback(author, why)
                        notes[goal.key].tries += 1
                        continue
                    await bb.commit(nxt)
                    took = True
                    continue
                if edit.kind == "hoist":
                    lifted = await bb.look(insert_above(bb.board.text, first_graded, edit.block))
                    kept = not classify(lifted.messages)[3]
                    # Measured on putnam_2020_a2: a hoisted lemma was false at j = 0;
                    # its statement is audited like a `have` before it enters the file.
                    bad = await asking.audit(author, bb.board, lifted) if kept else ""
                    kept = kept and not bad
                    events.append({"kind": "lemma", "by": author, "name": edit.name,
                                   "accepted": kept})
                    if not kept:
                        notes[goal.key].said = Feedback(
                            author, bad or format_messages(lifted.messages)[:FEEDBACK_CHARS])
                        notes[goal.key].tries += 1
                        continue
                    await bb.commit(lifted)
                    took = True
                    fresh = next((g for g in bb.board.goals if g.decl == edit.name), None)
                    if fresh and edit.body.strip():
                        nxt, why = await asking.advance(bb.board, fresh, edit.body, author)
                        events.append({"kind": "step", "by": author, "accepted": nxt is not None,
                                   **({} if nxt is not None else {"why": str(why)[:160]})})
                        if nxt is not None:
                            await bb.commit(nxt)
                        else:
                            notes[fresh.key].said = Feedback(author, why)
                    continue
                if edit.kind == "prove":
                    # The whole proof of a named declaration replaces what it had.
                    # Measured on p09: appended, it doubled its own opening; dropped,
                    # it was the best turn of the run.
                    fresh_text, at = restate(bb.board.text, edit.name)
                    if at < 0:
                        continue
                    opened = await bb.look(fresh_text)
                    target = opened.goals[at] if at < len(opened.goals) else None
                    events.append({"kind": "route", "by": author, "to": edit.name})
                    if target is None:
                        continue
                    nxt, why = await asking.advance(opened, target, edit.body, author)
                    if nxt is None and here is not None and edit.name == here.decl:
                        # The header was an echo and the body continues from here.
                        nxt, why = await asking.advance(bb.board, here, edit.body, author)
                    events.append({"kind": "step", "by": author, "accepted": nxt is not None,
                                   **({} if nxt is not None else {"why": str(why)[:160]})})
                    if nxt is None:
                        notes[goal.key].said = Feedback(author, why)
                        notes[goal.key].tries += 1
                        continue
                    await bb.commit(nxt)
                    took = True
            return took






        def prompt_for(goal: Goal, model: str, skeleton: bool = False,
                       plan: str | None = None) -> str:
            source, line = view(*render(bb.board.text, bb.board.index(goal))[:1], goal.decl)
            plan = notes[goal.key].plan if plan is None else plan
            parts = [f"Problem: {problem.description}".strip(),
                     "File:\n" + source[-FILE_CHARS:],
                     "What Lean reports as open, with its hypotheses. The first goal "
                     f"is the active one, at `skip` on line {line}:\n"
                     f"{goal.text[:GOAL_CHARS]}"]
            if notes[goal.key].hint:
                parts.append(notes[goal.key].hint)
            sheet = "\n".join(x for x in (sheet_for(goal.text), notes[goal.key].shelved) if x)
            if sheet:
                parts.append("Names the loaded Mathlib has for this goal's vocabulary, "
                             f"as #check prints them:\n{sheet}")
            if plan:
                parts.append("A mathematician was asked how to prove this goal and "
                             f"answered:\n{plan}")
            if notes[goal.key].said:
                parts.append(f"{notes[goal.key].said.lead(model)}:\n{notes[goal.key].said.text}")
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

        async def worker(model: str) -> None:
            idle, faults = 0, 0
            while budget.time_left() > 0 and budget.can_ask() and not finished:
                try:
                    if await turn(model):
                        idle = 0
                    else:
                        idle += 1
                        if idle > 3 and not notes.busy() and not bb.board.goals:
                            events.append({"stage": "stop", "note": "no goal left to work on"})
                            return
                        try:
                            await asyncio.wait_for(bb.changed.wait(), IDLE_WAIT_S)
                        except asyncio.TimeoutError:
                            pass
                except (BudgetExceeded, BudgetAccountingError, LeanRuntimeError, LLMCallError):
                    raise
                except Exception as exc:  # noqa: BLE001 - one bad turn must not zero the problem
                    faults += 1
                    events.append({"stage": "worker_error", "by": model,
                                   "error": f"{type(exc).__name__}: {exc}"[:200]})
                    if faults >= 3:
                        return

        async def turn(model: str) -> bool:
            """One turn for one worker: False when there was no goal to take."""

            nonlocal finished
            if True:
                async with lock:
                    if any(delivery.done_text(b) is not None for b in bb.branches):
                        finished = True
                        return True
                    if bb.all_last_in_line() or bb.stalled() or bb.exhausted():
                        drained = bb.exhausted()
                        await ladder.unstick()
                        if drained:
                            # The board moved (or could not): the models may be
                            # asked once more, with the new feedback in front of them.
                            notes.forget_repeats()
                    picked = bb.pick(model)
                    goal = picked[1] if picked else None
                    if picked:
                        bb.focus(picked[0])
                    base = bb.board
                    if goal is not None and goal.stmt in bb.proven and not notes[goal.key].recalled:
                        notes[goal.key].recalled = True
                        nxt, _ = await asking.judge(base, goal, bb.proven[goal.stmt])
                        if nxt is not None:
                            events.append({"kind": "recall", "goal": goal.text[-120:]})
                            await bb.commit(nxt)
                            return True
                    if goal is not None and not notes[goal.key].swept:
                        notes[goal.key].swept = True
                        if await ladder.sweep(goal) or await ladder.leaf_sweep(goal) or await ladder.witness_sweep(goal) \
                                or await ladder.generalise_sweep(goal):
                            return True
                    if goal is not None and not notes[goal.key].searched \
                            and notes[goal.key].tries >= SEARCH_AFTER:
                        # Measured over 70 runs: `apply?` and the name scan took
                        # 19% of the wall clock under the lock (601 probes, 22
                        # goals closed; 269 scans at 22 s), and Lean is busy
                        # 60-74% of a run. A goal the first step closes never pays.
                        notes[goal.key].searched = True
                        if await ladder.library_sweep(goal):
                            return True
                        await asking.consult(goal)
                    if goal is not None:
                        notes.claim(goal.key, model)
                        wants_plan = (notes[goal.key].tries >= PLAN_AFTER
                                      and not notes[goal.key].plan)
                        prompt = prompt_for(goal, model)
                if goal is not None and wants_plan:
                    # The crux is where routes diverge, so it gets two: one plan
                    # from each model, the second written as a skeleton onto a
                    # sibling branch. Lean's progress on each decides between them.
                    other = next((m for m in models if m != model), model)
                    state = State(text=bb.board.text, goal=goal.text)
                    avoid = list(routes.get(goal.decl, []))
                    plan, second = await asyncio.gather(
                        self._ask_plan(problem, state, services, ledger, other, avoid=avoid),
                        self._ask_plan(problem, state, services, ledger, model, avoid=avoid))
                    ask_second, fork = "", None
                    async with lock:
                        notes[goal.key].plan = plan
                        routes.setdefault(goal.decl, []).extend(
                            p for p in (plan, second) if p.strip())
                        events.append({"kind": "plan", "by": other, "chars": len(plan)})
                        events.append({"kind": "plan", "by": model, "chars": len(second)})
                        now = bb.live(base.bid)
                        moved = now.find(goal.key) if now else None
                        if moved:
                            bb.focus(now)
                            goal = moved
                        prompt = prompt_for(goal, model, skeleton=True) if moved else ""
                        if prompt:
                            events.append({"kind": "skeleton", "by": model})
                        if moved and second.strip() and second.strip() != plan.strip() \
                                and len(bb.branches) < BEAM + 1:
                            fork = Board(now.text, list(now.goals), list(now.messages),
                                         now.accepted, ladder.next_bid)
                            ladder.next_bid += 1
                            bb.sound[fork.bid] = bb.sound.get(now.bid, now.text)
                            bb.branches.append(fork)
                            bb.focus(fork)
                            ask_second = prompt_for(goal, model, skeleton=True, plan=second)
                            bb.focus(now)
                    if ask_second and fork is not None:
                        reply_b, _ = await self._call(model, ask_second, step_tokens(model),
                                                      services, ledger, system=BOARD_SYSTEM)
                        async with lock:
                            side = bb.live(fork.bid)
                            there = side.find(goal.key) if side else None
                            took = False
                            if there is not None:
                                bb.focus(side)
                                edits = interpret(reply_b, bb.board, there, graded)
                                took = await apply(model, there, edits) if edits else False
                            if took and bb.live(fork.bid):
                                events.append({"stage": "route", "from": base.bid,
                                               "to": fork.bid, "by": model})
                                bb.prune()
                            elif bb.live(fork.bid):
                                bb.branches.remove(bb.live(fork.bid))
                            main = bb.live(base.bid)
                            if main:
                                bb.focus(main)
                    if not prompt:
                        async with lock:
                            notes[goal.key].claimed_by = None
                        return True
                if goal is None:
                    return False
                task = asyncio.ensure_future(
                    self._call(model, prompt, step_tokens(model), services, ledger, system=BOARD_SYSTEM))
                asking.loose.append(task)
                try:
                    reply, why = await task
                finally:
                    asking.loose.remove(task)
                async with lock:
                    if notes[goal.key].claimed_by == model:
                        notes[goal.key].claimed_by = None
                    if why == "length":
                        reply = salvage(reply)
                        kept = reply.count("\n") + 1 if reply else 0
                        events.append({"kind": "cut", "by": model, "kept": kept})
                        if not kept:
                            notes[goal.key].said = Feedback(model, notes[goal.key].said.text
                                                            if notes[goal.key].said else "nothing yet", "cut")
                            notes[goal.key].tries += 1
                            return True
                    now = bb.live(base.bid)
                    here = now.find(goal.key) if now else None
                    if here is not None:
                        bb.focus(now)
                    elif base.find(goal.key) is not None and len(bb.branches) < BEAM + 1:
                        # The goal moved on under this reply. Judged against the
                        # file it was asked about, an accepted answer is a second
                        # way forward, and a second way is a branch, not waste.
                        fork = Board(base.text, list(base.goals), list(base.messages),
                                     base.accepted, ladder.next_bid)
                        ladder.next_bid += 1
                        bb.sound[fork.bid] = bb.sound.get(base.bid, base.text)
                        bb.branches.append(fork)
                        bb.focus(fork)
                        here = fork.find(goal.key)
                        edits = interpret(reply, bb.board, here, graded)
                        took = await apply(model, here, edits) if edits else False
                        if took and bb.live(fork.bid):
                            events.append({"stage": "fork", "from": base.bid, "to": fork.bid,
                                           "goal": goal.text[:60]})
                            bb.prune()
                        else:
                            if bb.live(fork.bid):
                                bb.branches.remove(bb.live(fork.bid))
                            events.append({"kind": "stale", "by": model})
                        return True
                    if here is None:
                        events.append({"kind": "stale", "by": model})
                        return True
                    edits = interpret(reply, bb.board, here, graded)
                    if not edits:
                        events.append({"kind": "empty", "by": model})
                        notes[goal.key].said = Feedback(model, notes[goal.key].said.text
                                                        if notes[goal.key].said else "nothing yet", "empty")
                        notes[goal.key].tries += 1
                        return True
                    await apply(model, here, edits)
                    still = bb.board.find(goal.key)
                    if still is not None and notes[goal.key].tries >= WITHDRAW_AFTER:
                        if settled_inside(bb.board.text, still) >= 2 and not notes[still.key].leaf_restarted:
                            # Measured on rmo_2000_6 (win54): one stuck case took the
                            # have with h2a, h5a and 2 closed cases down. The leaf
                            # restarts once before proved work is withdrawn.
                            notes[still.key].leaf_restarted = True
                            notes.forget(still.key)
                            events.append({"kind": "leaf_restart", "by": model, "goal": still.text[-160:],
                                           "settled": settled_inside(bb.board.text, still)})
                        else:
                            await bb.take_back(model, still)
                return True

        try:
            ladder.cocktail = await usable_cocktail(services)
            for candidate in sweep_files(problem.challenge, ladder.cocktail) + split_files(
                    problem.challenge, ladder.cocktail):
                if budget.time_left() <= 0:
                    break
                check = await services.lean.check_file(candidate)
                if check.accepted and not scoring_faults(candidate, names, problem.challenge):
                    events.append({"stage": "sweep", "accepted": True})
                    won = await delivery.deliver(candidate, "deterministic_sweep")
                    if won:
                        return won
                    delivery.offer(candidate, True)
                    return delivery.result(candidate, "deterministic_sweep", True)

            if graded_theorems(problem.challenge) > 1 and budget.can_ask():
                text = await self._share(problem, text, services, ledger, events)
            if definition_slots(text) and budget.can_ask():
                text = await self._define(problem, text, services, ledger, events)
            if names and budget.can_ask():
                text = await self._resolve_answers(
                    problem, text, names, services, ledger, events)

            bb.board = Board(text, bid=0)
            await bb.commit(await bb.look(text))
            tasks = [asyncio.ensure_future(worker(m)) for m in models]
            try:
                await asyncio.gather(*tasks)
            finally:
                finished = True
                await asyncio.wait(tasks, timeout=LOOSE_DRAIN_S)

            done = [t for t in (delivery.done_text(b) for b in bb.branches) if t is not None]
            if done:
                won = await delivery.deliver(done[0], "board_loop")
                if won:
                    return won
            if bb.branches:
                bb.board = min(bb.branches, key=lambda b: b.score)
            delivery.offer(bb.board.text, False)
            return delivery.result(delivery.best, "best_effort", False)
        except (BudgetExceeded, BudgetAccountingError, LeanRuntimeError, LLMCallError) as exc:
            events.append({"stage": "abort", "error": type(exc).__name__})
            return delivery.result(delivery.best, "aborted", False)
        finally:
            # Every call the agent started must settle before it returns: the
            # harness fails a problem whose ledger still holds a reservation.
            if asking.loose:
                await asyncio.wait(list(asking.loose))


def create_agent() -> BoardAgent:
    return BoardAgent()
