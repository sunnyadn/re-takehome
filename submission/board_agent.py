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
# A goal this many rejections deep is still open, only last in line. Time and
# money are the exits; a goal is never declared hopeless by count alone.
LAST_IN_LINE = 6
# A goal inside a `have ... := by` that has been rejected this many times takes
# the `have` down with it, and everything after it in its block: the board goes
# back to before the decomposition. Measured on rmo_2000_2: a false `have`
# posted at t=64 made every later goal a contradiction and the lemma unprovable.
WITHDRAW_AFTER = 4
# A board that has accepted nothing for this share of the window is stuck
# whatever its counts say. Measured on p09 (reg61b): 7 of 30 steps accepted,
# both withdrawals on one route, and the clock ran out before the counts did.
STALL_SHARE = 0.12
# When every goal is last in line, the declaration holding the worst of them
# goes back to its statement, with its goals' history cleared. Time and money
# bound how often; a count did not, and the branch was unreachable until v7.40.
# A worker with no goal to take waits this long for the board to change.
IDLE_WAIT_S = 2.0
# What the model is told when its step ran the whole check into the timeout.
# A block that does not parse desynchronises the parser for the rest of the
# file (measured on rmo_2000_6: one unclosed bracket, 1151 `Unknown identifier`
# messages over 82 checks of its prefixes and retries). Only the parse error is
# worth reading, and no shorter cut of the same text parses either.
PARSE_FAULT = "that block does not parse, so Lean read nothing after the fault: "
TIMED_OUT = ("that step timed out: the file no longer checks in time. The tactic "
             "is far too expensive (decide, omega or nlinarith over a large range, "
             "simp with a wide lemma set); the step was removed. Use interval_cases "
             "on a bounded variable, or state the cases as a disjunction and prove "
             "each with norm_num")




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


# A step that makes the file slower to check by this much is refused as too
# expensive even when Lean raises no budget error: every later check pays it,
# and the comparator allows 180s. Measured on p09: one accepted step took the
# check from 1s to 38s, and the run then lost 5 minutes to a 120s timeout and
# the container restart that follows it.
SLOW_STEP_MS = 10_000
# The whole file, not one step: the comparator recompiles cold on 4 cores in
# 180 s, and a 24 s warm p09 file timed out there. Measured on rmo_2000_2
# (4-core pod): 318 checks, 2229 s of 2645 s in Lean, 5 timeouts, 5 restarts.
CHECK_CAP_MS = 25_000
# A leaf is one cell the comparator compiles once; its own cost is not a per-step
# tax. Measured on rmo_2001_2 (frame123): the difference-of-squares leaf takes
# 12 s idle and 50 s on a loaded host, and was cut by the 30 s timeout.
LEAF_CAP_MS = 90_000
# There is no refutation probe. Proving `¬ target` from the context by
# decide/omega only refutes the goal when the context is consistent, and a
# proof by contradiction lives in an inconsistent one: on p09 the probe
# "refuted" six true goals (`h1 : n % 3 = 1 ... ⊢ False`) and undid the proof.
# Live branches: alternative proof files racing on the same problem. A second
# accepted answer to a goal one model already moved becomes a sibling branch
# rather than a stale reply. Measured on p09: the run was decided by one such
# choice at t=50s, and there was no way to hedge it.
BEAM = 2


























META = re.compile(r"\?[\w.]+|^(?:Type|Sort)\b")






AUDIT_TOKENS = 2500
# An auditor that has not answered by then lets the step through as unverified;
# the call runs on and is drained before the agent returns (a reservation left
# open fails the problem). Measured: one 482 s audit reply under the board lock.
AUDIT_WAIT_S = 120.0
AUDIT_SYSTEM = ("You audit one goal inside a Lean 4 proof. You answer with one "
                "JSON object and nothing else.")




























































TUPLE_IN = re.compile(r"[⟨(]\s*([A-Za-z_][\w']*(?:\s*,\s*[A-Za-z_][\w']*)+)\s*[⟩)]\s*∈")




































INFLATION = 3.0






























































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
        loose: list[asyncio.Task[Any]] = []
        lock = asyncio.Lock()
        changed = asyncio.Event()
        notes = run.notes
        budget = Budget(run)
        delivery = Delivery(self, run, budget)
        progress_at = budget.started

        restated: dict[str, int] = {}
        withdrawn: dict[str, list[str]] = {}
        audited: dict[tuple[str, str], str] = {}
        finished = False









        board = Board(text)
        branches: list[Board] = []
        sound: dict[int, str] = {}
        next_bid = 1

        def focus(b: Board) -> None:
            nonlocal board
            board = b

        def live(bid: int) -> Board | None:
            return next((b for b in branches if b.bid == bid), None)

        def prune() -> None:
            while len(branches) > BEAM:
                worst = max(branches, key=lambda b: b.score)
                branches.remove(worst)
                events.append({"stage": "prune", "bid": worst.bid, "goals": len(worst.goals)})

        cells = run.cells
        # Statement → the block that closed a cell stating it. A closed cell is
        # a proof of a theorem; withdrawing what enclosed it does not unprove
        # it (measured on rmo_2001_2: the final goal, closed at 67 s, came back
        # as new after the enclosing have was withdrawn and was never reclosed).
        proven: dict[str, str] = {}

        def remember_closed(b: Board) -> None:
            lines = b.text.split("\n")
            for sp in all_cell_spans(b.text):
                stmt = cells.statements.get(sp.id)
                if not stmt or stmt in proven or any(sp.holds(g.line) for g in b.goals):
                    continue
                body = [l[sp.indent:] if len(l) - len(l.lstrip()) >= sp.indent else l.lstrip()
                        for l in lines[sp.start:sp.end]]
                block = strip_markers("\n".join(body))
                if block.strip() and "sorry" not in block:
                    proven[stmt] = block
                    events.append({"stage": "proven", "cell": sp.id, "stmt": stmt[-80:], "lines": block.count("\n") + 1})


        dissolved = 0

        heavy = {"leaf": False}   # set while a leaf block is judged

        async def look(candidate: str, base: Board | None = None,
                       focus: int | str | None = None, edited: Goal | None = None) -> Board:
            """The board after one Lean check: the whole file as cells, or, with
            a focus, that one cell (or proof) checked and the rest inherited."""
            nonlocal dissolved

            old = base_region(base, focus, edited) if base is not None and focus is not None else None
            if focus is not None and old is None:
                focus = None
            rendered = render_check(candidate, cells, focus)
            timeout_s = CHECK_TIMEOUT_CAP_S if heavy["leaf"] else check_timeout_s((base or board).ms)
            check = await services.lean.check_file(blank_techniques(rendered.text), timeout_s=timeout_s)
            messages = remap(check.messages, rendered.lines)
            errors = [m for m in messages if isinstance(m, dict) and m.get("severity") == "error"]
            dump_check(rendered.text, focus, check)
            for m in check.messages:
                if m.get("severity") == "error" and str(m.get("data", "")).startswith("unexpected"):
                    at = message_line(m) or 0
                    shown = rendered.text.split("\n")
                    events.append({"stage": "render_fault", "said": str(m.get("data"))[:80],
                                   "lines": shown[max(at - 2, 0):at + 1]})
                    break
            if focus is None:
                # An error on a marker line is the cell's own header or its link
                # failing, not the proof: that cell goes back inline.
                at = {message_line(m) for m in errors}
                broken = [sp for sp in all_cell_spans(candidate) if sp.start in at]
                if broken and dissolved < 8:
                    dissolved += len(broken)
                    text = candidate
                    for sp in broken:
                        events.append({"stage": "inline", "cell": sp.id, "why": "link"})
                        text = dissolve(text, sp.id)
                    return await look(text, base)
            # As the kit's: no error, no `sorry` anywhere (a `sorry` inside a line is
            # no placeholder, and the grader rejects sorryAx; measured on p10: a
            # board with none open delivered a file the comparator refused).
            accepted = not check.timed_out and not errors and not re.search(r"\bsorry\b", candidate)
            found = read_board(candidate, messages, accepted)
            found.ms = check.duration_ms
            if rendered.region is not None and base is not None and old is not None:
                new = rendered.region
                if isinstance(focus, int) and not any(new[0] <= g.line <= new[1] for g in found.goals) \
                        and not errors:
                    # The cell closed: what encloses it is checked next, so a goal
                    # of the parent that has no placeholder (Lean reports it on
                    # the parent's header) is seen again. Measured on rmo_2000_6:
                    # the stale-report filter alone let `case refine_1.refine_2`
                    # vanish and the board was delivered with a sorry.
                    above = [sp for sp in all_cell_spans(candidate) if sp.holds(new[0]) and sp.id != focus]
                    parent: int | str = max(above, key=lambda sp: sp.start).id if above else owner(candidate, new[0])
                    if parent and parent != focus:
                        return await look(candidate, base, parent, edited)
                # Fresh goals are the placeholders this check rendered as probes;
                # every other placeholder (outside the unit, or inside a nested
                # cell that was a stub here) keeps its goal from the base, by order.
                shown = rendered.text.split("\n")
                probed = {rendered.lines[i] for i, l in enumerate(shown) if CELL_PROBE in l}
                nested_old = {sp.id for sp in all_cell_spans(base.text)} - ({focus} if isinstance(focus, int) else set())
                outside_old = [g for g in base.goals
                               if not old[0] <= g.line <= old[1]
                               or (g.cell in nested_old and g.cell != 0)]
                outside_new = [g for g in found.goals if g.line not in probed]
                if len(outside_old) != len(outside_new):
                    return await look(candidate, base)
                delta = (new[1] - new[0]) - (old[1] - old[0])
                goals = []
                carried = iter(outside_old)
                for g in found.goals:
                    if g.line in probed:
                        goals.append(g)
                        continue
                    was = next(carried)
                    goals.append(Goal(g.line, g.indent, g.decl, was.text, was.stmt, g.cell))
                kept = []
                holes = [g.line for g in goals if g.line not in probed]
                inner_old = {g.line for g in base.goals if old[0] <= g.line <= old[1]
                             and g.cell in nested_old and g.cell != 0}
                for m in base.messages:
                    at = message_line(m)
                    if at is None or (old[0] <= at <= old[1] and not (
                            m in classify([m])[0] and any(
                                (message_span(m) or (at, at))[0] <= h <= (message_span(m) or (at, at))[1]
                                for h in inner_old))):
                        continue
                    cut = edited.line if edited is not None else old[0]
                    m = shift_message(m, delta) if at > cut else m
                    span = message_span(m)
                    if m in classify([m])[0] and span and not any(span[0] <= h <= span[1] for h in holes):
                        # A goal report from before the edit that no placeholder
                        # outside the checked unit sits under is about the goal
                        # just closed (measured: `exact Nat.sum_range_choose_halfway k`
                        # closed the theorem and its old header report made
                        # `unreachable` refuse the step).
                        continue
                    kept.append(m)
                found = Board(candidate, goals, kept + messages, accepted, base.bid, check.duration_ms)
            for g in found.goals:
                if g.stmt:
                    notes[g.key].known_stmt = g.stmt
            found.goals = [g if g.stmt or not notes[g.key].known_stmt else
                           Goal(g.line, g.indent, g.decl, g.text, notes[g.key].known_stmt, g.cell)
                           for g in found.goals]
            return found

        async def probe(text: str, line: int, timeout_s: int) -> tuple[list[dict[str, Any]], int]:
            """One check of the file with a probe line in it, focused on the cell
            or proof that holds the line; messages in file coordinates, and ms."""
            held = enclosing(text, line)
            focus: int | str | None = held.id if held else (owner(text, line) or None)
            rendered = render_check(text, cells, focus)
            check = await services.lean.check_file(blank_techniques(rendered.text), timeout_s=timeout_s)
            return remap(check.messages, rendered.lines), check.duration_ms

        async def commit(candidate: Board, progress: bool = True) -> None:
            """Make a board current, after its own housekeeping. Every commit
            but a restart or a withdrawal is progress for the stall clock."""

            nonlocal board, progress_at
            if progress:
                progress_at = time.monotonic()
            bid = board.bid
            fresh = await settle(candidate)
            fresh.bid = bid
            inherit(board.goals, fresh.goals, notes)
            _, _, dear, broken = classify(fresh.messages)
            if broken or dear:
                if fresh.text != sound.get(bid, ""):
                    events.append({"stage": "repair", "bid": bid,
                                   "why": "cost" if dear and not broken else "error",
                                   "said": format_messages(broken or dear)[:300]})
                    fresh = await look(sound.get(bid, text))
                    fresh.bid = bid
            else:
                sound[bid] = fresh.text
                remember_closed(fresh)
            board = fresh
            for i, b in enumerate(branches):
                if b.bid == bid:
                    branches[i] = fresh
                    break
            else:
                branches.append(fresh)
            finished_text = delivery.done_text(board)
            delivery.offer(finished_text or board.text, finished_text is not None)
            changed.set()
            changed.clear()

        async def settle(candidate: Board) -> Board:
            """A placeholder with no goal is dropped; a goal with no placeholder
            gets one; several goals behind one placeholder each get their own."""

            for _ in range(4):
                _, spare, dear, broken = classify(candidate.messages)
                surplus = [l for l in (message_line(m) for m in spare) if l]
                idle = [g.line for g in candidate.goals if not g.text]
                if surplus or (idle and not dear and not broken):
                    candidate = await look(drop_lines(candidate.text, surplus or idle))
                    continue
                for goal in candidate.goals:
                    if goal.text.count("⊢") >= 2 and not notes[goal.key].divided:
                        notes[goal.key].divided = True
                        apart = split_cursor(candidate.text, goal.text, candidate.index(goal))
                        if apart:
                            events.append({"stage": "split", "goals": goal.text.count("⊢")})
                            candidate = await look(apart)
                            break
                else:
                    return candidate
            return candidate

        failed_at = 0
        last_span = (0, 0)
        known_names: dict[str, str] = {}
        # The environment's answer to a goal's vocabulary, once per token set.
        shelf: dict[tuple[str, ...], str] = {}
        # Every plan asked for a declaration, kept across restarts: the next
        # plan is asked to differ from them.
        routes: dict[str, list[str]] = {}

        async def consult(goal: Goal) -> None:
            """Ask the loaded Mathlib what it has for this goal's words, once."""
            tokens = tuple(goal_tokens(goal.text))
            if len(tokens) < 2:
                return
            if tokens not in shelf:
                if not budget.affordable("scan"):
                    return
                imports = "\n".join(l for l in text.split("\n") if l.startswith("import "))
                check = await services.lean.check_file(library_file(imports, tokens), timeout_s=90)
                budget.spent("scan", check.duration_ms / 1000)
                shelf[tokens] = read_library(check.messages)
                events.append({"stage": "library", "tokens": list(tokens),
                               "lines": shelf[tokens].count("\n") + bool(shelf[tokens]),
                               "ms": check.duration_ms})
            notes[goal.key].shelved = shelf[tokens]

        async def nearest_names(messages: Sequence[dict[str, Any]], goal: Goal) -> str:
            """Lean's own answer to a misspelt library name, once per name."""
            names = library_names(messages, goal.text)
            fresh = [n for n in names if n not in known_names]
            if fresh and budget.affordable("scan"):
                imports = "\n".join(l for l in text.split("\n") if l.startswith("import "))
                check = await services.lean.check_file(name_probe_file(imports, fresh), timeout_s=90)
                budget.spent("scan", check.duration_ms / 1000)
                found = read_name_probe(check.messages)
                for n in fresh:
                    part = next((p for p in found.split("\n\n") if p.startswith(n + " ")), "")
                    known_names[n] = part
                events.append({"stage": "names", "asked": fresh, "ms": check.duration_ms,
                               "found": bool(found)})
            return "\n".join(known_names[n] for n in names if known_names.get(n))

        async def judge(base: Board, goal: Goal, block: str) -> tuple[Board | None, str]:
            """One edit at one goal, judged against the whole file; an edit that
            only ran out of Lean's budget is judged once more with the budget
            raised, whoever wrote it (a leaf as much as a model step)."""

            nxt, why = await judge_once(base, goal, block)
            if nxt is None and why == BUDGET_RETRY and RAISED_BUDGETS not in base.text:
                lifted = await look(insert_preamble(base.text, RAISED_BUDGETS), base)
                moved = lifted.find(goal.key)
                if moved:
                    events.append({"stage": "budget", "decl": goal.decl})
                    nxt, why = await judge_once(lifted, moved, block)
            return nxt, why

        async def judge_once(base: Board, goal: Goal, block: str) -> tuple[Board | None, str]:
            """`failed_at` keeps the block-relative line of the first error, for
            the prefix cut."""

            nonlocal failed_at, last_span
            splittable = goal.stmt and not notes[goal.key].unsplittable and not is_root_goal(base.text, goal)
            cell_id = cells.new(goal.stmt) if splittable else None
            focus: int | str = cell_id if cell_id is not None else (goal.cell or goal.decl)

            async def placed(trailing: bool) -> tuple[str, tuple[int, int], Board]:
                nonlocal cell_id, focus
                candidate, span = put(base.text, goal, block, trailing, cell_id)
                nxt = await look(candidate, base, focus, goal)
                if cell_id is not None and any(message_line(m) == span[0] for m in classify(nxt.messages)[3]):
                    # The statement Lean printed does not elaborate on its own
                    # (measured: a set literal loses its `: Set _`). A literal
                    # is ascribed from the binder types once; failing that, the
                    # block stays inside what encloses it and the goal is not
                    # split again (measured on putnam_2018_a1: 128 such retries).
                    repaired = ascribe_literals(goal.stmt)
                    if repaired != goal.stmt and repaired not in tried_statements:
                        tried_statements.add(repaired)
                        cells.statements[cell_id] = repaired
                        nxt = await look(candidate, base, focus, goal)
                    if any(message_line(m) == span[0] for m in classify(nxt.messages)[3]):
                        events.append({"stage": "inline", "cell": cell_id, "decl": goal.decl})
                        notes[goal.key].unsplittable = True
                        cell_id, focus = None, goal.cell or goal.decl
                        candidate, span = put(base.text, goal, block, trailing)
                        nxt = await look(candidate, base, focus, goal)
                    else:
                        notes[goal.key].known_stmt = repaired
                return candidate, span, nxt

            candidate, span, nxt = await placed(True)
            _, surplus, expensive, failures = classify(nxt.messages)
            closing = False
            if not failures and {message_line(m) for m in surplus if in_span(m, span)} == {span[1]}:
                # Only the trailing placeholder has no goal: the step closed it.
                candidate, span, nxt = await placed(False)
                _, surplus, expensive, failures = classify(nxt.messages)
                closing = True
            last_span = span
            lines = [l for l in (message_line(m) for m in failures) if l and span[0] <= l <= span[1]]
            failed_at = (min(lines) - span[0]) if lines else 0
            if any("TIMEOUT" in str(m.get("data")) for m in failures):
                # Measured on putnam_2018_a1: a timed-out check cost 120s plus a
                # container restart, and the prefix cut then paid it again.
                return None, TIMED_OUT
            if expensive and not failures:
                return None, BUDGET_RETRY
            over_cap = nxt.ms > CHECK_CAP_MS and nxt.ms - base.ms > SLOW_STEP_MS // 5
            if heavy["leaf"] or closing:
                # A closed goal is never re-elaborated by a later focused check;
                # only the comparator's cold compile pays it (measured on
                # rmo_2001_2: seven closing steps refused at 12-13 s from 0.2 s).
                over_cap = nxt.ms > LEAF_CAP_MS
            if not failures and ((nxt.ms - base.ms > SLOW_STEP_MS and not (heavy["leaf"] or closing)) or over_cap):
                events.append({"stage": "slow", "ms": nxt.ms, "was": base.ms})
                return None, (f"that step makes the file take {nxt.ms // 1000}s to "
                              f"check, up from {base.ms // 1000}s; every later step "
                              "pays that" + (f", and past {CHECK_CAP_MS // 1000}s the judge's "
                              "cold compile times out" if over_cap else "") +
                              ". Use a cheaper tactic: a targeted rw or "
                              "exact, not simp with a wide lemma set or decide")
            parse = [m for m in failures if str(m.get("data", "")).startswith("unexpected")]
            if parse:
                return None, PARSE_FAULT + format_messages(parse[:1])[:FEEDBACK_CHARS]
            if failures or expensive:
                # Every other open goal is an `unsolved goals` error too; the
                # model is told about its own step, not the rest of the board.
                own = [m for m in nxt.messages
                       if m in failures or m in expensive or in_span(m, span)]
                said_text = format_messages(own)[:FEEDBACK_CHARS]
                names = await nearest_names(own, goal)
                return None, f"{said_text}\n{names}\n{notes_for(said_text)}".strip()
            lost = unreachable(nxt.messages, nxt.text, -1)
            if lost and lost[0] >= span[1]:
                # A goal outside the step's own lines that no placeholder reaches
                # (a `case` block took its sibling, the step closed the last hole
                # under a header report): it gets a placeholder where Lean says it
                # is, and the step stands. Measured on rmo_2000_6: the closing step
                # was refused for a goal it had not touched.
                reopened = await look(reopen_past_cell(nxt.text, *lost), base)
                if not classify(reopened.messages)[3] and not unreachable(reopened.messages, reopened.text, -1):
                    events.append({"stage": "reopen", "line": lost[0], "decl": goal.decl})
                    nxt, lost = reopened, None
            if lost:
                return None, ("that step left a goal open inside a branch nothing "
                              "can get back to. A step that splits the goal gives "
                              "every branch its own `sorry`, or closes it outright")
            if any(in_span(m, span) for m in surplus):
                return None, ("there are no goals left where that step was written: "
                              "the goal was already closed above it")
            left = [g for g in nxt.goals if span[0] <= g.line <= span[1]]
            if left and all(g.text == goal.text for g in left):
                return None, "that step left the goal exactly as it was"
            if any(g.text.count("✝") > goal.text.count("✝") for g in left):
                # Measured on p10: `have h2 ...` accepted 18 times over, each one
                # shadowing the last, and the goal text never the same twice.
                return None, ("that step re-declared a name the context already "
                              "has (Lean shows the old one as `h✝`); use the "
                              "existing hypothesis instead of stating it again")
            if any(target_of(g.text) == "False" and target_of(goal.text) != "False"
                   and hyp_count(g.text) <= hyp_count(goal.text) for g in left):
                # Measured on rmo_2001_2: a wrong witness left `hp : Nat.Prime 3,
                # hq : Nat.Prime 11 ⊢ False` and 14 turns went into it.
                return None, ("that step turned the goal into `False` without adding "
                              "a hypothesis, so the context is still consistent and "
                              "`False` cannot be proved: the witness, rewrite or case "
                              "was wrong. Undo it and choose again")
            if left and max(inflated(goal.text, g.text) for g in left) >= INFLATION:
                # Measured on rmo_2001_2, p09 and rmo_2000_2 (5 runs): a rewrite
                # `at *` unfolded a variable in every hypothesis and both models
                # then worked on the unfolded form for the rest of the run.
                return None, ("that step made the existing hypotheses more than "
                              f"{INFLATION:g}× larger without closing the goal (a rewrite "
                              "unfolded a variable everywhere). Rewrite only the "
                              "hypothesis you need, or state the fact you want as a `have`")
            if any(META.search(target_of(g.text)) for g in left):
                # Measured on rmo_2000_2: `apply lt_irrefl _` left `⊢ Type ?u.350`
                # and `⊢ Preorder ?α`; each got a sorry and 30 turns, six deep.
                return None, ("that step left a goal Lean could not infer (`Type ?u`, "
                              "`?α`): an `apply` with `_` for arguments it cannot fill. "
                              "Give the term in full, e.g. `exact absurd h1 (not_lt.mpr h2)`")
            if any(len(VACUOUS.findall(g.text)) > len(VACUOUS.findall(goal.text)) for g in left):
                # Measured on p09: `simp ... at h ⊢` left `h : True ⊢ False`, Lean
                # had no complaint, and five turns went into a goal that was dead.
                return None, ("that step turned a hypothesis into `True` (or `Type`), "
                              "which throws the fact away; rewrite without `at h`, "
                              "or use the fact instead of simplifying it")
            return nxt, ""

        async def audit(author: str, base: Board, nxt: Board) -> str:
            """Every statement a step writes is tried against a witness: Lean
            states it, the auditor names values, Lean checks that they satisfy
            every hypothesis and break it. The refutation, or "" to let it in."""

            if not cfg.audit:
                return ""

            # Measured over 12 audits: a narrating model names values that violate
            # a hypothesis every time, at ~9 s; the other answers in ~1.4 s.
            other = next((m for m in models if m != author and not narrates(m)),
                         next((m for m in models if not narrates(m)),
                              next((m for m in models if m != author), author)))
            had = {g.key for g in base.goals}
            lines = nxt.text.split("\n")
            # Measured on putnam_2020_a2: a false `have` with a proof body had only
            # its residue audited. The claim is audited whatever the body says.
            known: dict[str, dict[str, str]] = {}
            subjects: list[dict[str, Any]] = []
            for i, ln in enumerate(lines):
                head = HAVE_HEAD.match(ln)
                decl = owner(nxt.text, i + 1) if head else ""
                claim = " ".join(claim_of(head.group(2).strip()).split()) if head else ""
                if not decl or not claim:
                    continue
                if decl not in known:
                    known[decl] = stated_facts(base.text, decl)
                if claim in known[decl]:
                    continue
                subjects.append({"key": (decl, "have " + claim), "decl": decl, "at": i,
                                 "what": head.group(2).strip(), "claim": claim})
            covered = {s["at"] for s in subjects}
            for g in nxt.goals:
                # `⊢ False` is provable only in an inconsistent context, so a witness
                # for the context alone proves the branch dead. Measured on p09: a
                # satisfiable `⊢ False` held both models for the rest of the run.
                # A goal with nothing in scope is a closed proposition: a wrong
                # witness or rewrite leaves one that is false, and its negation
                # decides it in one check. Measured on rmo_2000_6: `use 10; use 1`
                # left `⊢ 0 < 1 ∧ 2000 ∣ 10 ^ 3 * 1 ^ 4 ∧ ...` and the branch died.
                dead_end = target_of(g.text) == "False"
                closed = is_closed(g.text)
                if (g.key in had or not g.text or META.search(target_of(g.text))
                        or not (dead_end or closed or is_stated(lines, g))
                        or enclosing_have(lines, g)[0] in covered):
                    continue
                subjects.append({"key": g.key, "decl": g.decl, "goal": g, "what": "",
                                 "claim": ""})
            for sub in subjects:
                if audited.get(sub["key"]):
                    return audited[sub["key"]]
            subjects = [sub for sub in subjects if sub["key"] not in audited]
            if not subjects or not budget.can_ask():
                return ""
            goals = [sub for sub in subjects if "goal" in sub]
            haves = [sub for sub in subjects if "at" in sub]
            for sub in goals:
                sub["stmt"] = sub["goal"].stmt
            unstated = [sub for sub in goals if not sub["stmt"]]
            if unstated:
                said_ = statements((await probe(
                    extract_file(nxt.text, [sub["goal"] for sub in unstated]),
                    unstated[0]["goal"].line, check_timeout_s(nxt.ms)))[0])
                for sub in unstated:
                    sub["stmt"] = said_.get(sub["goal"].line, "")
            if haves:
                text, where = have_extract_file(lines, [sub["at"] for sub in haves])
                said_ = statements((await probe(text, where.get(haves[0]["at"], 1), check_timeout_s(nxt.ms)))[0])
                for sub in haves:
                    sub["stmt"] = said_.get(where.get(sub["at"], -1), "")
            # Definitions only: a hoisted lemma's proof would be paid again.
            roots = root_names(nxt.text)
            first = proof_span(nxt.text, roots[0]) if roots else None
            prefix = nxt.text[:first[0]] if first else ""
            shown_prefix = without_techniques(prefix)[0].replace("import Mathlib", "")
            for sub in subjects:
                sub["parsed"] = split_statement(sub["stmt"]) if sub.get("stmt") else None
            # Evaluation first: a claim it breaks needs no auditor.
            for sub in subjects:
                sub["searched"], sub["found"] = False, None
                if sub["parsed"] and sub["parsed"][0]:
                    sub["searched"], sub["found"] = await self._enumerated(prefix, *sub["parsed"], services)
            # No binders, no question: the witness file alone decides a closed claim.
            # A claim the walk covered is settled: the auditor is asked about the rest.
            asked = [sub for sub in subjects
                     if sub["parsed"] and sub["parsed"][0] and not sub["found"] and not sub["searched"]]
            pending_calls = [asyncio.ensure_future(self._call(
                other, audit_prompt(sub["stmt"], shown_prefix),
                AUDIT_TOKENS, services, ledger, system=AUDIT_SYSTEM)) for sub in asked]
            for t in pending_calls:
                loose.append(t)
                t.add_done_callback(lambda t: loose.remove(t) if t in loose else None)
            if pending_calls:
                done_calls, late = await asyncio.wait(pending_calls, timeout=AUDIT_WAIT_S)
                if late:
                    events.append({"kind": "slow_call", "by": other, "audits": len(late),
                                   "waited_s": AUDIT_WAIT_S})
            replies = [t.result() if t.done() else ("", "") for t in pending_calls]
            for sub in subjects:
                audited[sub["key"]] = ""
                verdict, values = "unstated", {}
                target = sub["claim"] or target_of(sub["goal"].text)
                if sub["parsed"]:
                    groups, target = sub["parsed"]
                    reply, stopped = replies[asked.index(sub)] if sub in asked else ("", "")
                    names = {n for grp in groups for n in binder_names(grp)}
                    given = sub["found"] if sub["found"] else read_witness(reply)
                    values = {n: v for n, v in (given or {}).items() if n in names}
                    verdict = "unverified"
                    if given is None and stopped != "length" and "holds" in reply:
                        verdict = "holds"
                    if sub["searched"] and not sub["found"]:
                        verdict = "holds"
                    if sub["found"] and "sequence" in sub["found"]:
                        # Lean evaluated the sampled sequence itself: the hit is the verdict.
                        verdict, values = "refuted", dict(sub["found"])
                    elif values or not names:
                        check = await services.lean.check_file(
                            witness_file(prefix, groups, values, target),
                            timeout_s=CHECK_TIMEOUT_FLOOR_S)
                        if check.accepted:
                            verdict = "refuted"
                events.append({"kind": "audit",
                               "by": "evaluation" if sub.get("searched") else other,
                               "goal": target[:100], "verdict": verdict, "values": values})
                if verdict == "refuted":
                    stmt = sub["what"] or f"⊢ {target}"
                    if sub["claim"]:
                        withdrawn.setdefault(sub["decl"], []).append(claim_of(sub["what"]))
                    at = ", ".join(f"{n} = {v}" for n, v in values.items())
                    audited[sub["key"]] = (
                        f"`{stmt}` is false, so the step was not posted: with {at} every "
                        "hypothesis in scope holds and it fails (Lean checked this). Do "
                        "not restate it; state a fact that is true at those values too"
                        if values else
                        f"that step left the goal `{stmt}`, which is false (Lean decided "
                        "it): the witness, rewrite or case was wrong. Undo it and choose again")
                    return audited[sub["key"]]
            return ""

        async def mine(base: Board, goal: Goal, block: str, author: str,
                       why: str) -> tuple[Board | None, str]:
            """The statements of a rejected block, posted as `sorry` facts at
            the goal. A statement Lean cannot elaborate or the audit refutes is
            dropped and the rest tried once more; the feedback stays the step's."""

            heads = mine_statements(block, stated_facts(base.text, goal.decl),
                                    withdrawn.get(goal.decl, []))
            if len(heads) < 2:
                return None, why
            for _ in range(2):
                skeleton = "\n".join(f"{h}\n  sorry" for h in heads)
                nxt, said_ = await judge(base, goal, skeleton)
                bad = await audit(author, base, nxt) if nxt is not None else ""
                if nxt is not None and not bad:
                    events.append({"kind": "mined", "by": author, "facts": len(heads)})
                    return nxt, ""
                if nxt is None:
                    at = failed_at // 2 if failed_at else -1
                    keep = [h for i, h in enumerate(heads) if i != at]
                else:
                    keep = [h for h in heads if claim_of(h[:-len(" := by")]).strip() not in bad]
                if len(keep) < 2 or keep == heads:
                    break
                heads = keep
            return None, why

        async def advance(base: Board, goal: Goal, block: str,
                          author: str) -> tuple[Board | None, str]:
            """A step, then its prefixes, then `exact?` in place of a bad proof."""

            opening = block.strip().split("\n")[0].strip()
            if opening and opening in undone.get(goal.decl, []) and not opening.startswith("have "):
                # Measured on rmo_2000_6: a cell reset nine times, the model
                # re-writing the same opening step each time.
                return None, (f"`{opening[:80]}` was tried here and taken back after the goals "
                              "under it went nowhere; open with a different step")
            nxt, why = await judge(base, goal, block)
            if nxt is None and why not in (BUDGET_RETRY, TIMED_OUT) and not why.startswith(PARSE_FAULT):
                # The first error's line says where to cut; one check instead of
                # eight. Measured: 3.7 checks per model call, most of them here.
                cuts = prefixes(block)
                guided = [c for c in cuts if c.count("\n") + 1 <= max(failed_at, 1)]
                order = guided[:1] + [c for c in cuts if c not in guided[:1]]
                tried = 0
                while order and tried < 3:
                    shorter = order[0]
                    tried += 1
                    nxt, _ = await judge(base, goal, shorter)
                    if nxt is not None:
                        events.append({"kind": "prefix", "by": author,
                                       "lines": shorter.count("\n") + 1})
                        why = ""
                        break
                    order = order[len(order) // 2 + 1:] if len(order) > 1 else []
                retry = hand_to_search(block)
                if nxt is None and retry != block and budget.affordable("retry"):
                    # `exact?` costs ~27 s a call here and leaves 2 GB of index in
                    # the container (measured, p10); it has a share of its own so
                    # it cannot starve `apply?` on a stuck goal (measured on
                    # rmo_2000_6: 9 retries used the scan share by 250 s and
                    # `10 ≤ a * b` then waited 40 minutes for Nat.le_of_dvd).
                    t0 = time.monotonic()
                    nxt, _ = await judge(base, goal, retry)
                    budget.spent("retry", time.monotonic() - t0)
                    events.append({"kind": "search-retry", "by": author,
                                   "accepted": nxt is not None})
                if nxt is None:
                    nxt, why = await mine(base, goal, block, author, why)
            if nxt is None and why == BUDGET_RETRY:
                why = ("the step exceeded Lean's elaboration budget even at a "
                       "raised budget; make it cheaper")
            # Every board that leaves here is audited, whichever path accepted it.
            # Measured on rmo_2000_6: a prefix cut carried a false claim past it.
            if nxt is not None:
                bad = await audit(author, base, nxt)
                if bad:
                    return None, bad
                return nxt, ""
            return nxt, why

        async def sweep(goal: Goal) -> bool:
            """The free closers, once per goal. (`exact?` used to follow: measured
            1 of 51 goals closed over 24 runs, and a slow one restarts the container.)"""

            base = board
            block = tagged_closers(cocktail)
            t0 = time.monotonic()
            nxt, _ = await judge(base, goal, block)
            events.append({"kind": "closers", "by": "harness", "accepted": nxt is not None,
                           "ms": int((time.monotonic() - t0) * 1000)})
            if nxt is None:
                return False
            tactic = fired_closer(nxt.messages, last_span, cocktail)
            flat = None
            if tactic:
                cell_id = cells.new(goal.stmt) if goal.stmt and not is_root_goal(base.text, goal) else None
                flat = await look(put(base.text, goal, tactic, trailing=False, cell_id=cell_id)[0],
                                  base, cell_id if cell_id is not None else (goal.cell or goal.decl), goal)
            if flat is not None and flat.find(goal.key) is None and not any(
                    classify(flat.messages)[2:]):
                nxt = flat
            events.append({"kind": "collapse", "tactic": tactic, "accepted": nxt is flat})
            await commit(nxt)
            return True

        async def witness_sweep(goal: Goal) -> bool:
            """An existential with a decidable body: Lean enumerates the witnesses
            and the first tuple that closes the goal is written, no model asked.
            Measured on rmo_2000_6: both models guessed `use 10, 1` and `use 2, 4`
            for 12 minutes; the only small witness is a = 1, b = 10."""

            parsed = existential(goal.text)
            if not parsed:
                return False
            names, body = parsed
            imports = "\n".join(l for l in text.split("\n") if l.startswith("import "))
            check = await services.lean.check_file(witness_search_file(imports, names, body), timeout_s=60)
            found = read_witnesses(check.messages)
            accepted = False
            for row in found:
                for closer in ("norm_num", "decide"):
                    block = f"exact ⟨{', '.join(row)}, by {closer}⟩"
                    nxt, _ = await judge(board, goal, block)
                    if nxt is not None:
                        await commit(nxt)
                        accepted = True
                        break
                if accepted:
                    break
            if found:
                # Kept even when the goal closed: the same goal on a sibling
                # branch is not swept again (same key) and reads it from the prompt.
                notes[goal.key].hint = ("Evaluation over 0 ≤ " + ", ".join(names) + f" < {WITNESS_BOUND} found "
                                   "these values satisfy the body: " + "; ".join(
                                       ", ".join(f"{n} = {v}" for n, v in zip(names, row)) for row in found)
                                   + (f". `{block}` closed it." if accepted else ""))
            events.append({"kind": "witnesses", "goal": goal.text[-160:], "found": found,
                           "accepted": accepted, "ms": check.duration_ms})
            return accepted

        async def leaf_sweep(goal: Goal) -> bool:
            """Tactic blocks built from the goal's shape (leaves.py), each one
            check, no model asked. Measured on 3 September: three of the four
            unsolved problems were lost on leaves of these shapes after the
            models had found the route."""

            base = board
            candidates = leaf_candidates(goal.text) if cfg.leaves else []
            if not candidates or not budget.affordable("leaf"):
                return False
            t0 = time.monotonic()
            tried = 0
            heavy["leaf"] = True
            try:
                for block in candidates:
                    tried += 1
                    nxt, why = await judge(base, goal, block)
                    if nxt is not None:
                        events.append({"kind": "leaf", "goal": goal.text[-120:],
                                       "block": block.split("\n")[-1][:80], "accepted": True,
                                       "ms": int((time.monotonic() - t0) * 1000)})
                        await commit(nxt)
                        return True
                    if why == TIMED_OUT or not budget.affordable("leaf"):
                        break
                events.append({"kind": "leaf", "goal": goal.text[-120:], "accepted": False,
                               "tried": tried, "ms": int((time.monotonic() - t0) * 1000)})
                return False
            finally:
                heavy["leaf"] = False
                budget.spent("leaf", time.monotonic() - t0)

        conjectured: dict[tuple[str, str], str] = {}
        tried_statements: set[str] = set()
        undone: dict[str, list[str]] = {}

        async def generalise_sweep(goal: Goal) -> bool:
            """A sum identity in one variable that its own induction did not
            close: the variable's other occurrences are generalised, each family
            tabulated in Lean and fitted to a shape, a fit that holds below
            VERIFY is posted as a lemma (the induction leaf proves it) and the
            goal rewrites by it. Measured: putnam_2020_a2, 0/32 model proposals."""

            target = target_of(goal.text)
            if goal.decl.startswith("vm_conj_") or "h_gen" in hypotheses(goal.text) or not budget.affordable("leaf"):
                return False
            ks = _sum_variables(leaf_hyps(goal.text), target)
            halves = split_top(target, " = ")
            if not ks or halves is None or "=" in halves[0] or "=" in halves[1]:
                return False
            k, lhs = ks[0], halves[0].strip()
            taken = set(hypotheses(goal.text)) | set(re.findall(r"[A-Za-z_][\w']*", target))
            fresh = next((c for c in ("n", "m", "t", "a", "b") if c not in taken), "vm_n")
            fams = families(lhs, k, fresh)
            roots = root_names(board.text)
            first = proof_span(board.text, roots[0]) if roots else None
            prefix = board.text[:first[0]] if first else ""
            found = [(f, g) for (f, g) in conjectured if f in fams]
            if not found:
                t0 = time.monotonic()
                for i, fam in enumerate(fams[:6]):
                    check = await services.lean.check_file(
                        blank_techniques(table_file(prefix, fam, fresh, k, i)), timeout_s=60)
                    table = read_table(check.messages)
                    if not table:
                        continue
                    for guess in fits(table, fresh, k, fam)[:2]:
                        check = await services.lean.check_file(
                            blank_techniques(verify_file(prefix, fam, guess, fresh, k)), timeout_s=60)
                        if verified(check.messages):
                            found.append((fam, guess))
                budget.spent("leaf", time.monotonic() - t0)
                events.append({"stage": "conjecture", "goal": target[:100], "families": len(fams),
                               "fits": [g for _, g in found][:3]})
            if not found:
                return False
            fam, guess = found[0]
            name = conjectured.setdefault((fam, guess), f"vm_conj_{len(conjectured) + 1}")
            text = board.text
            if name not in root_names(text):
                text = insert_preamble(text, lemma_text(name, fresh, k, fam, guess))
            staged = await look(text) if text != board.text else board
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
                nxt, _ = await judge(staged, moved, f"{fact}\nrw [h_gen]")
                if nxt is None:
                    nxt, _ = await judge(staged, moved, fact)
                if nxt is not None:
                    break
            events.append({"stage": "generalise", "lemma": name, "guess": guess,
                           "rewritten": nxt is not None})
            await commit(nxt if nxt is not None else staged)
            left = next((g for g in board.goals if g.decl == goal.decl and "h_gen" in hypotheses(g.text)), None)
            if left is not None and not notes[left.key].searched:
                # Mathlib may state the rewritten goal outright (Nat.sum_range_choose_halfway).
                notes[left.key].searched = True
                await library_sweep(left, force=True)
            return True

        async def library_sweep(goal: Goal, force: bool = False) -> bool:
            """Mathlib asked what unifies with the goal (`apply?`), after the
            closers failed. An `exact` answer is written, no model asked; the
            rest go into the prompt as the names that fit. Measured in the
            image: 4 of 4 leaf goals closed by exact, about 8 s each."""

            if not force and not budget.affordable("scan"):
                return False
            # The file's own check time plus the heartbeat-capped search.
            answered, took = await probe(apply_file(board.text, goal), goal.line, check_timeout_s(board.ms) + 30)
            budget.spent("scan", took / 1000)
            found = read_suggestions(answered, goal.line)
            accepted = False
            for how, term in found:
                if how != "exact":
                    continue
                nxt, _ = await judge(board, goal, f"exact {term}")
                if nxt is not None:
                    await commit(nxt)
                    accepted = True
                    break
            if found and not accepted:
                notes[goal.key].hint = ("Mathlib's `apply?` on this goal suggested: " + "; ".join(
                    f"`{how} {term}`" for how, term in found[:3]) + ". Those unify with the goal; the ?_ holes are what is left to prove.")
            events.append({"kind": "library", "goal": goal.text[-120:], "found": len(found),
                           "accepted": accepted, "ms": took})
            return accepted

        async def take_back(author: str, goal: Goal, why: str = "") -> bool:
            """The `have` this goal is the body of comes off the board, with the
            rest of its block; the goal it was posted on is told why. True when
            the board changed."""
            why = why or f"after {WITHDRAW_AFTER} failed attempts to prove it"

            fresh, statement = withdraw_only(board.text, goal)
            if not fresh and goal.decl and goal.decl not in graded:
                # A hoisted lemma has no enclosing have; it goes as a whole when
                # its goal keeps failing, if the file still stands without it.
                # Measured on rmo_2000_6: rmo_2000_6_part1 : IsLeast S 20 (false,
                # undecidable for the audit) sat on the board with nothing to take it back.
                span = proof_span(board.text, goal.decl)
                head = DECL_HEAD.match(board.text[span[0]:span[1]]) if span else None
                dropped = drop_declaration(board.text, goal.decl)
                trimmed = await look(dropped)
                if head and not classify(trimmed.messages)[3]:
                    statement = head.group(1).strip()
                    events.append({"kind": "withdraw", "by": author, "decl": goal.decl,
                                   "have": statement[:120], "tries": notes[goal.key].tries})
                    for g in graded:
                        withdrawn.setdefault(g, []).append(statement)
                    await commit(trimmed, progress=False)
                    return True
                return False
            if not fresh:
                return False
            # Only the have goes; if Lean then finds the rest of the block broken
            # (it used the name), the rest goes too. Measured on rmo_2000_6:
            # withdrawing h_witness took h_min, the whole crux, which never used it.
            trimmed = await look(fresh)
            whole = False
            if classify(trimmed.messages)[3]:
                fresh, statement = withdraw(board.text, goal)
                trimmed, whole = await look(fresh), True
            events.append({"kind": "withdraw", "by": author, "have": statement[:120],
                           "tries": notes[goal.key].tries, "whole_block": whole})
            withdrawn.setdefault(goal.decl, []).append(statement)
            await commit(trimmed, progress=False)
            back = next((g for g in reversed(board.goals) if g.decl == goal.decl
                         and g.line <= goal.line), None)
            if back is not None:
                notes[back.key].said = Feedback(
                    author, f"`{statement}` was posted here as a `have` and withdrawn "
                    f"{why}. The board is "
                    "back to before it. Do not restate that fact; prove this goal "
                    "another way, or through facts that are easier to prove", "withdrawn")
            return True

        async def lift_and_advance(base: Board, goal: Goal, block: str,
                                   author: str) -> tuple[Board | None, str]:
            """A fact posted with `sorry` inside a `have` goes above the outermost
            `have`: facts live at the shallowest scope. Measured on rmo_2000_2:
            skeletons nested 7 deep, 25 open goals, withdraw never firing."""

            lines = base.text.split("\n")
            chain = enclosing_chain(lines, goal)
            facts, rest = split_facts(block)
            if not chain or not facts:
                return await advance(base, goal, block, author)
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
                    nxt, why = await advance(staged, moved, rest, author)
                else:
                    nxt, why = await look(text, base), ""
                    if classify(nxt.messages)[3]:
                        nxt, why = None, format_messages(classify(nxt.messages)[3])[:FEEDBACK_CHARS]
                    elif nxt is not None:
                        bad = await audit(author, base, nxt)
                        if bad:
                            nxt, why = None, bad
                if nxt is not None or not any(n in local for n in UNKNOWN_NAME.findall(why)):
                    break
            else:
                depth = 0
            if nxt is None and depth == 0:
                return await advance(base, goal, block, author)
            if nxt is None:
                return None, (why + f"\n(a fact stated inside `{head.group(2).strip()[:60]}` "
                              "is posted before that `have`, at the top of the proof; it can "
                              "only use the theorem's variables and the facts above it)")
            events.append({"kind": "lifted", "by": author, "facts": len(lifted),
                           "dup": len(dup), "from_depth": len(chain), "to_depth": depth})
            if dup:
                notes[goal.key].said = Feedback(author, "already on the board: " + ", ".join(
                    f"`{n}`" for _, n in dup), "lifted")
            return nxt, ""

        async def apply(author: str, goal: Goal, edits: list[Edit]) -> bool:
            """Every edit a reply asked for, each against the board as it stands."""

            took = False
            for edit in edits:
                here = board.find(goal.key)
                if edit.kind == "probe":
                    printed = await self._probe(State(text=board.text), edit.body, services)
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
                    if restates(edit.body, withdrawn.get(here.decl, ())):
                        events.append({"kind": "restated", "by": author})
                        notes[goal.key].said = Feedback(author, "that step restates a fact "
                                                  "already withdrawn from this declaration")
                        notes[goal.key].tries += 1
                        continue
                    present = proved_facts(board.text, here)
                    if restates(edit.body, present):
                        # Measured on p09: the same claim proved twice in one declaration.
                        names = [present[c] for c in present if restates(edit.body, [c])]
                        events.append({"kind": "restated", "by": author, "of": names[:3]})
                        notes[goal.key].said = Feedback(author, "that step states a fact already "
                                                  "on the board as " + ", ".join(f"`{n}`" for n in names[:3])
                                                  + "; use it, do not prove it again")
                        notes[goal.key].tries += 1
                        continue
                    nxt, why = await lift_and_advance(board, here, edit.body, author)
                    if nxt is None:
                        notes[here.key].refused.add(edit.body)
                    events.append({"kind": "step", "by": author, "accepted": nxt is not None,
                                   **({} if nxt is not None else {"why": str(why)[:160]})})
                    if nxt is None:
                        notes[goal.key].said = Feedback(author, why)
                        notes[goal.key].tries += 1
                        continue
                    await commit(nxt)
                    took = True
                    continue
                if edit.kind == "hoist":
                    lifted = await look(insert_above(board.text, first_graded, edit.block))
                    kept = not classify(lifted.messages)[3]
                    # Measured on putnam_2020_a2: a hoisted lemma was false at j = 0;
                    # its statement is audited like a `have` before it enters the file.
                    bad = await audit(author, board, lifted) if kept else ""
                    kept = kept and not bad
                    events.append({"kind": "lemma", "by": author, "name": edit.name,
                                   "accepted": kept})
                    if not kept:
                        notes[goal.key].said = Feedback(
                            author, bad or format_messages(lifted.messages)[:FEEDBACK_CHARS])
                        notes[goal.key].tries += 1
                        continue
                    await commit(lifted)
                    took = True
                    fresh = next((g for g in board.goals if g.decl == edit.name), None)
                    if fresh and edit.body.strip():
                        nxt, why = await advance(board, fresh, edit.body, author)
                        events.append({"kind": "step", "by": author, "accepted": nxt is not None,
                                   **({} if nxt is not None else {"why": str(why)[:160]})})
                        if nxt is not None:
                            await commit(nxt)
                        else:
                            notes[fresh.key].said = Feedback(author, why)
                    continue
                if edit.kind == "prove":
                    # The whole proof of a named declaration replaces what it had.
                    # Measured on p09: appended, it doubled its own opening; dropped,
                    # it was the best turn of the run.
                    fresh_text, at = restate(board.text, edit.name)
                    if at < 0:
                        continue
                    opened = await look(fresh_text)
                    target = opened.goals[at] if at < len(opened.goals) else None
                    events.append({"kind": "route", "by": author, "to": edit.name})
                    if target is None:
                        continue
                    nxt, why = await advance(opened, target, edit.body, author)
                    if nxt is None and here is not None and edit.name == here.decl:
                        # The header was an echo and the body continues from here.
                        nxt, why = await advance(board, here, edit.body, author)
                    events.append({"kind": "step", "by": author, "accepted": nxt is not None,
                                   **({} if nxt is not None else {"why": str(why)[:160]})})
                    if nxt is None:
                        notes[goal.key].said = Feedback(author, why)
                        notes[goal.key].tries += 1
                        continue
                    await commit(nxt)
                    took = True
            return took

        def pick(model: str) -> tuple[Board, Goal] | None:
            """The best branch's least-tried unclaimed goal; with none unclaimed
            anywhere, one the other model holds, so a 158s reply does not idle
            the fast model. Measured on p09: 4 minutes of 20 went that way."""

            # A branch the other model is working on comes after the ones it is
            # not: with two routes open both workers went to the better-ranked
            # one and the other route got 2 turns in 40 (measured on rmo_2000_6).
            busy = {b.bid for b in branches for g in b.goals
                    if notes[g.key].claimed_by not in (None, model)}
            options = []
            for rank, b in enumerate(sorted(branches, key=lambda b: b.score)):
                for g in b.goals:
                    # A goal this model has already answered with a byte-identical
                    # rejected block is not offered to it again until the board
                    # changes (measured on rmo_2000_6: 1190 repeats in one run,
                    # runs of 125 while the other model was in a long call).
                    if g.text and notes[g.key].claimed_by != model and author_free(notes[g.key], model):
                        options.append((notes[g.key].claimed_by is not None,
                                        b.bid in busy and len(branches) > 1, rank,
                                        notes[g.key].tries >= LAST_IN_LINE,
                                        notes[g.key].tries, g.line, b, g))
            if not options:
                return None
            first = min(options, key=lambda o: o[:6])
            return first[6], first[7]

        def exhausted() -> bool:
            """Every open goal answered with a repeat by every model: nothing
            more will come from asking, so the board has to change."""
            return bool(board.goals) and not notes.busy() and all(
                all(m in notes[g.key].repeated for m in cfg.lines) for g in board.goals)

        def all_last_in_line() -> bool:
            return bool(board.goals) and not notes.busy() and all(
                notes[g.key].tries >= LAST_IN_LINE for g in board.goals)

        def stalled() -> bool:
            """Nothing accepted for STALL_SHARE of the window, no worker mid-step."""
            return bool(board.goals) and not notes.busy() and (
                time.monotonic() - progress_at > STALL_SHARE * cfg.time_limit_s)

        async def unstick() -> None:
            """Every goal last in line, or nothing accepted for a while: the
            innermost open have comes off on a fork, else the worst goal's
            declaration starts over and what was said and planned for it goes."""

            nonlocal next_bid

            worst = max(board.goals, key=lambda g: notes[g.key].tries, default=None)
            if worst is None or not worst.decl:
                return
            # Measured on rmo_2000_6 (one55a 08:46→08:51): one goal left, 6 tries,
            # and the declaration went back to its statement. Goals sitting among
            # proved facts restart themselves once before the declaration does.
            leaves = [g for g in board.goals if not notes[g.key].leaf_restarted
                      and settled_inside(board.text, g) >= 2]
            if leaves:
                for g in leaves:
                    notes[g.key].leaf_restarted = True
                    notes.forget(g.key)
                events.append({"kind": "leaf_restart", "by": "harness", "goals": len(leaves),
                               "settled": settled_inside(board.text, leaves[0])})
                return
            # The innermost open `have` goes first and its siblings stay: undo at
            # the goal, not the declaration. The declaration restarts only when
            # no open goal sits inside a `have` any more.
            inside = [g for g in board.goals if withdraw_only(board.text, g)[0]]
            if inside:
                deepest = max(inside, key=lambda g: (len(g.indent), notes[g.key].tries))
                # The stuck subtree is not thrown away: the board with it stays
                # as a sibling branch and the take-back happens on a fork, so
                # the two ways forward race, as two plans do.
                if len(branches) < BEAM + 1:
                    fork = Board(board.text, list(board.goals), list(board.messages),
                                 board.accepted, next_bid)
                    next_bid += 1
                    sound[fork.bid] = sound.get(board.bid, board.text)
                    branches.append(fork)
                    focus(fork)
                    events.append({"stage": "fork", "from": branches[0].bid if branches else 0,
                                   "to": fork.bid, "why": "stall"})
                if await take_back("harness", deepest,
                                   "after the board made no progress for a while"):
                    prune()
                    return
            # A goal inside a cell: that cell alone goes back to its `sorry`
            # (its block was one step's answer), the rest of the proof stays.
            held = enclosing(board.text, worst.line)
            if held is not None:
                if len(branches) < BEAM + 1:
                    fork = Board(board.text, list(board.goals), list(board.messages),
                                 board.accepted, next_bid)
                    next_bid += 1
                    sound[fork.bid] = sound.get(board.bid, board.text)
                    branches.append(fork)
                    focus(fork)
                    events.append({"stage": "fork", "from": branches[0].bid if branches else 0,
                                   "to": fork.bid, "why": "reset"})
                events.append({"stage": "reset", "cell": held.id, "decl": worst.decl,
                               "tries": notes[worst.key].tries})
                notes.forget(worst.key)
                first_line = board.text.split("\n")[held.start].strip()
                undone.setdefault(worst.decl, []).append(first_line)
                await commit(await look(reset_cell(board.text, held)), progress=False)
                prune()
                return
            restated[worst.decl] = restated.get(worst.decl, 0) + 1
            fresh_text, _ = restate(board.text, worst.decl)
            events.append({"stage": "restate", "decl": worst.decl,
                           "tries": notes[worst.key].tries})
            notes.forget_decl(worst.decl)
            await commit(await look(fresh_text), progress=False)

        def prompt_for(goal: Goal, model: str, skeleton: bool = False,
                       plan: str | None = None) -> str:
            source, line = view(*render(board.text, board.index(goal))[:1], goal.decl)
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
                        if idle > 3 and not notes.busy() and not board.goals:
                            events.append({"stage": "stop", "note": "no goal left to work on"})
                            return
                        try:
                            await asyncio.wait_for(changed.wait(), IDLE_WAIT_S)
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

            nonlocal finished, next_bid
            if True:
                async with lock:
                    if any(delivery.done_text(b) is not None for b in branches):
                        finished = True
                        return True
                    if all_last_in_line() or stalled() or exhausted():
                        drained = exhausted()
                        await unstick()
                        if drained:
                            # The board moved (or could not): the models may be
                            # asked once more, with the new feedback in front of them.
                            notes.forget_repeats()
                    picked = pick(model)
                    goal = picked[1] if picked else None
                    if picked:
                        focus(picked[0])
                    base = board
                    if goal is not None and goal.stmt in proven and not notes[goal.key].recalled:
                        notes[goal.key].recalled = True
                        nxt, _ = await judge(base, goal, proven[goal.stmt])
                        if nxt is not None:
                            events.append({"kind": "recall", "goal": goal.text[-120:]})
                            await commit(nxt)
                            return True
                    if goal is not None and not notes[goal.key].swept:
                        notes[goal.key].swept = True
                        if await sweep(goal) or await leaf_sweep(goal) or await witness_sweep(goal) \
                                or await generalise_sweep(goal):
                            return True
                    if goal is not None and not notes[goal.key].searched \
                            and notes[goal.key].tries >= SEARCH_AFTER:
                        # Measured over 70 runs: `apply?` and the name scan took
                        # 19% of the wall clock under the lock (601 probes, 22
                        # goals closed; 269 scans at 22 s), and Lean is busy
                        # 60-74% of a run. A goal the first step closes never pays.
                        notes[goal.key].searched = True
                        if await library_sweep(goal):
                            return True
                        await consult(goal)
                    if goal is not None:
                        notes.claim(goal.key, model)
                        wants_plan = (notes[goal.key].tries >= PLAN_AFTER
                                      and not notes[goal.key].plan)
                        ask = prompt_for(goal, model)
                if goal is not None and wants_plan:
                    # The crux is where routes diverge, so it gets two: one plan
                    # from each model, the second written as a skeleton onto a
                    # sibling branch. Lean's progress on each decides between them.
                    other = next((m for m in models if m != model), model)
                    state = State(text=board.text, goal=goal.text)
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
                        now = live(base.bid)
                        moved = now.find(goal.key) if now else None
                        if moved:
                            focus(now)
                            goal = moved
                        ask = prompt_for(goal, model, skeleton=True) if moved else ""
                        if ask:
                            events.append({"kind": "skeleton", "by": model})
                        if moved and second.strip() and second.strip() != plan.strip() \
                                and len(branches) < BEAM + 1:
                            fork = Board(now.text, list(now.goals), list(now.messages),
                                         now.accepted, next_bid)
                            next_bid += 1
                            sound[fork.bid] = sound.get(now.bid, now.text)
                            branches.append(fork)
                            focus(fork)
                            ask_second = prompt_for(goal, model, skeleton=True, plan=second)
                            focus(now)
                    if ask_second and fork is not None:
                        reply_b, _ = await self._call(model, ask_second, step_tokens(model),
                                                      services, ledger, system=BOARD_SYSTEM)
                        async with lock:
                            side = live(fork.bid)
                            there = side.find(goal.key) if side else None
                            took = False
                            if there is not None:
                                focus(side)
                                edits = interpret(reply_b, board, there, graded)
                                took = await apply(model, there, edits) if edits else False
                            if took and live(fork.bid):
                                events.append({"stage": "route", "from": base.bid,
                                               "to": fork.bid, "by": model})
                                prune()
                            elif live(fork.bid):
                                branches.remove(live(fork.bid))
                            main = live(base.bid)
                            if main:
                                focus(main)
                    if not ask:
                        async with lock:
                            notes[goal.key].claimed_by = None
                        return True
                if goal is None:
                    return False
                task = asyncio.ensure_future(
                    self._call(model, ask, step_tokens(model), services, ledger, system=BOARD_SYSTEM))
                loose.append(task)
                try:
                    reply, why = await task
                finally:
                    loose.remove(task)
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
                    now = live(base.bid)
                    here = now.find(goal.key) if now else None
                    if here is not None:
                        focus(now)
                    elif base.find(goal.key) is not None and len(branches) < BEAM + 1:
                        # The goal moved on under this reply. Judged against the
                        # file it was asked about, an accepted answer is a second
                        # way forward, and a second way is a branch, not waste.
                        fork = Board(base.text, list(base.goals), list(base.messages),
                                     base.accepted, next_bid)
                        next_bid += 1
                        sound[fork.bid] = sound.get(base.bid, base.text)
                        branches.append(fork)
                        focus(fork)
                        here = fork.find(goal.key)
                        edits = interpret(reply, board, here, graded)
                        took = await apply(model, here, edits) if edits else False
                        if took and live(fork.bid):
                            events.append({"stage": "fork", "from": base.bid, "to": fork.bid,
                                           "goal": goal.text[:60]})
                            prune()
                        else:
                            if live(fork.bid):
                                branches.remove(live(fork.bid))
                            events.append({"kind": "stale", "by": model})
                        return True
                    if here is None:
                        events.append({"kind": "stale", "by": model})
                        return True
                    edits = interpret(reply, board, here, graded)
                    if not edits:
                        events.append({"kind": "empty", "by": model})
                        notes[goal.key].said = Feedback(model, notes[goal.key].said.text
                                                        if notes[goal.key].said else "nothing yet", "empty")
                        notes[goal.key].tries += 1
                        return True
                    await apply(model, here, edits)
                    still = board.find(goal.key)
                    if still is not None and notes[goal.key].tries >= WITHDRAW_AFTER:
                        if settled_inside(board.text, still) >= 2 and not notes[still.key].leaf_restarted:
                            # Measured on rmo_2000_6 (win54): one stuck case took the
                            # have with h2a, h5a and 2 closed cases down. The leaf
                            # restarts once before proved work is withdrawn.
                            notes[still.key].leaf_restarted = True
                            notes.forget(still.key)
                            events.append({"kind": "leaf_restart", "by": model, "goal": still.text[-160:],
                                           "settled": settled_inside(board.text, still)})
                        else:
                            await take_back(model, still)
                return True

        try:
            cocktail = await usable_cocktail(services)
            for candidate in sweep_files(problem.challenge, cocktail) + split_files(
                    problem.challenge, cocktail):
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

            board = Board(text, bid=0)
            await commit(await look(text))
            tasks = [asyncio.ensure_future(worker(m)) for m in models]
            try:
                await asyncio.gather(*tasks)
            finally:
                finished = True
                await asyncio.wait(tasks, timeout=LOOSE_DRAIN_S)

            done = [t for t in (delivery.done_text(b) for b in branches) if t is not None]
            if done:
                won = await delivery.deliver(done[0], "board_loop")
                if won:
                    return won
            if branches:
                board = min(branches, key=lambda b: b.score)
            delivery.offer(board.text, False)
            return delivery.result(delivery.best, "best_effort", False)
        except (BudgetExceeded, BudgetAccountingError, LeanRuntimeError, LLMCallError) as exc:
            events.append({"stage": "abort", "error": type(exc).__name__})
            return delivery.result(delivery.best, "aborted", False)
        finally:
            # Every call the agent started must settle before it returns: the
            # harness fails a problem whose ledger still holds a reservation.
            if loose:
                await asyncio.wait(list(loose))


def create_agent() -> BoardAgent:
    return BoardAgent()
