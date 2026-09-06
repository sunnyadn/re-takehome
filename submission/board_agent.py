"""A board of open goals, two models asking for steps at the same time, Lean
judging every edit against the whole file. Only the model calls overlap: every
Lean check in a turn runs under one lock, measured at 19% of the wall clock."""


from __future__ import annotations

import asyncio
import re
from typing import Any

from re_harness import AgentResult, LLMCallError, Problem, Services
from re_harness.budget import BudgetAccountingError, BudgetExceeded
from re_harness.lean import LeanRuntimeError

from typing import Sequence
from submission.framework import (answer_slots, as_goal, declaration_name, fill_answer,
                                  insert_preamble, statement_probes)
from submission.contract import declared_names
from submission.replies import printed_numbers
from submission.board.types import NARRATES, STEP_TOKENS
from submission.techniques import without_techniques
from submission.contract import format_messages, in_file_coordinates, scoring_faults
from submission.sweep import split_files, sweep_files, usable_cocktail
from submission.framework import (classify, definition_slots, fill_definition, graded_theorems, line_of, placeholders, proof_span, root_names)
from submission.contract import strip_fences
from submission.config import ANSWER_TOKENS, Config, FEEDBACK_CHARS, FILE_CHARS, Ledger
from submission.board.types import Board, Goal, binder_names, narrates, owner, signature
from submission.board.reply import dialect, set_elements
from submission.run.budget import Budget
from submission.run.context import Run
from submission.run.delivery import Delivery
from submission.run.blackboard import Blackboard
from submission.run.asking import AUDIT_SYSTEM, AUDIT_TOKENS, Asking
from submission.run.ladder import Ladder
from submission.run.loop import Loop
from submission.board.text import drop_declaration, split_statement
from submission.calls import Caller, RenewingLean
from submission.sampling import enumerated
from submission.board.probes import CHECK_TIMEOUT_FLOOR_S, audit_prompt, extract_file, read_witness, statements, witness_file

LOOSE_DRAIN_S = 30.0

# There is no refutation probe. Proving `¬ target` from the context by
# decide/omega only refutes the goal when the context is consistent, and a
# proof by contradiction lives in an inconsistent one: on p09 the probe
# "refuted" six true goals (`h1 : n % 3 = 1 ... ⊢ False`) and undid the proof.


TUPLE_IN = re.compile(r"[⟨(]\s*([A-Za-z_][\w']*(?:\s*,\s*[A-Za-z_][\w']*)+)\s*[⟩)]\s*∈")


class BoardAgent:
    """The board program. `solve` is the spine; everything above it is a setup
    rewrite `solve` runs once, before the board opens."""

    def __init__(self, config: Config | None = None) -> None:
        self.config = config or Config.from_env()
        self.caller = Caller(self.config)


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
                said, _ = await self.caller.call(model, ask, ANSWER_TOKENS, services, ledger,
                                           think=not narrates(model))
                term = dialect(" ".join(strip_fences(said).split("\n")))[:FEEDBACK_CHARS].strip()
                if not term or term.startswith("by "):
                    note = "\n\nYour last reply was not a term."
                    continue
                candidate = fill_definition(text, name, term)
                check = await services.lean.check_file(candidate)
                if classify(check.messages).failures:
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

    async def _shared_lemma(self, problem: Problem, text: str, services: Services,
                     ledger: Ledger, events: list[dict[str, Any]]) -> str:
        """The fact several theorems need, hoisted above them before any step.
        Both models are asked at once and every distinct statement that
        elaborates is kept: a true lemma costs nothing, and which form the
        proof wants (`%` or `[MOD]`) decided 4 of 6 p09 runs at t=50s."""

        ask = (f"Problem: {problem.description}\n\nFile:\n{text[:FILE_CHARS]}\n\n"
               f"These {graded_theorems(problem.challenge)} theorems are "
               "graded together and share their mathematics. Name the one fact "
               "more than one of them needs, and state it as a standalone Lean 4 "
               "`theorem` above them. Reply with one ```lean block holding that "
               "declaration and nothing else. Leave its body `sorry`; proving it "
               "is a later turn.")
        # Measured on p09 (6 of 6 runs): with reasoning on, qwen answered this
        # with a page of prose and no declaration; only gpt-oss's lemma stayed.
        replies = await asyncio.gather(*(
            self.caller.call(line, ask, STEP_TOKENS, services, ledger,
                       think=not any(n in line for n in NARRATES))
            for line in self.config.lines[:2]))
        for said, _ in replies:
            block = strip_fences(said).strip()
            named = declaration_name(block)
            if not named or named in declared_names(text):
                events.append({"stage": "share", "name": named, "kept": False})
                continue
            candidate = insert_preamble(text, as_goal(block) or block)
            check = await services.lean.check_file(candidate)
            kept = not classify(check.messages).failures
            events.append({"stage": "share", "name": named, "kept": kept})
            if kept:
                text = candidate
        return text

    async def _share(self, problem: Problem, text: str, services: Services,
                     ledger: Ledger, events: list[dict[str, Any]]) -> str:
        """As the framework's, and each kept statement is audited: a shared
        lemma that a witness breaks does not enter the file."""

        before = set(root_names(text))
        text = await self._shared_lemma(problem, text, services, ledger, events)
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
        searched, found = await enumerated(prefix, groups, target, services)
        if found and await breaks(found):
            return "refuted", found
        if searched:
            return "holds", {}
        auditor = next((m for m in self.config.lines if not narrates(m)), self.config.lines[0])
        reply, _ = await self.caller.call(auditor, audit_prompt(stmt, without_techniques(prefix)[0].replace("import Mathlib", "")),
                                    AUDIT_TOKENS, services, ledger, system=AUDIT_SYSTEM)
        given = {n: v for n, v in (read_witness(reply) or {}).items() if n in names}
        if (given or not names) and await breaks(given):
            return "refuted", given
        return ("holds" if tries or given or "holds" in reply else "unverified"), {}

    async def _resolve_answers(self, problem: Problem, text: str, names: Sequence[str],
                               services: Services, ledger: Ledger,
                               events: list[dict[str, Any]]) -> str:
        """An answer slot is a number to compute, never a number to guess.

        A slot left as `sorry` is unreachable by the cursor and banned by the
        grader, so an unfilled one is reported and asked for again."""

        # A slot left as `sorry` makes the theorem unprovable and the goal
        # display empty, so the loop that follows is worth nothing. Measured on
        # p10: 72 turns asked about a goal Lean could not print. Both models
        # get a turn at it before that happens.
        note = ""
        # A slot the statement equates to a closed term is evaluated here, no
        # model asked (measured on p06: both failed to write the `#eval`).
        own = statement_probes(text, answer_slots(text))
        if own:
            check = await services.lean.check_file(insert_preamble(text, "\n".join(own)))
            values = printed_numbers(check.messages)
            missing = answer_slots(text)
            for name, value in zip(missing, values):
                text = fill_answer(text, name, value)
            events.append({"stage": "probe", "by": "harness", "asked": list(missing),
                           "printed": values[:len(missing)], "unfilled": list(answer_slots(text))})
        for attempt in range(4):
            missing = answer_slots(text)
            if not missing:
                break
            ask = (f"Write one `#eval` line per name, in this order: {', '.join(missing)}.\n"
                   "Each must compute the value, not state it: search a range, or "
                   "evaluate the definition.\n\n"
                   f"Problem: {problem.description}\n\nFile:\n{text[:FILE_CHARS]}\n\n"
                   "Lean 4 with Mathlib. Output the `#eval` lines only. Each must print "
                   "one natural number and nothing else, so the whole search goes in "
                   "the expression: `#eval ((List.range 200).filter (fun n => P n))."
                   "getLast?.getD 0` for a largest, `.head?.getD 0` for a least. A "
                   "line that prints `true` or `some n` is not an answer." + note)
            asking = self.config.lines[attempt % len(self.config.lines)]
            reply, _ = await self.caller.call(
                asking, ask, ANSWER_TOKENS, services, ledger, think=True)
            probes = [l for l in strip_fences(reply).splitlines()
                      if l.strip().startswith("#eval")]
            if not probes:
                note = "\n\nYour last reply contained no `#eval` line."
                continue
            # Measured on p07: three `#eval` lines for one name, the answer and
            # two checks of it. The first printed value fills the slot, and a
            # slot filled wrong is a false theorem no later step can recover.
            if len(probes) != len(missing) and attempt < 2:
                note = (f"\n\nYour last reply had {len(probes)} `#eval` lines for "
                        f"{len(missing)}. Give exactly one per name, in that order, "
                        "and nothing else.")
                continue
            probes = probes[:len(missing)]
            check = await services.lean.check_file(insert_preamble(text, "\n".join(probes)))
            values = printed_numbers(check.messages)
            for name, value in zip(missing, values):
                text = fill_answer(text, name, value)
            left = answer_slots(text)
            events.append({"stage": "probe", "by": asking, "asked": list(missing),
                           "printed": values[:len(missing)], "unfilled": list(left)})
            note = (f"\n\nThese slots are still unfilled: {', '.join(left)}. Each `#eval` "
                    "must print one bare numeral." if left else "")
            if left and check.messages:
                note += "\nLean said:\n" + format_messages(check.messages)[:600]
        return text

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        services = in_file_coordinates(services)
        cfg = self.config
        events: list[dict[str, Any]] = []
        if not isinstance(services.lean, RenewingLean):
            services.lean = RenewingLean(services.lean, events)
        run = Run(problem, services, cfg, events)
        ledger, names = run.ledger, run.names
        budget = Budget(run)
        delivery = Delivery(run, budget)
        bb = Blackboard(run, budget, delivery)
        asking = Asking(self.caller, run, budget, bb)
        ladder = Ladder(run, budget, bb, asking)
        loop = Loop(self.caller, run, budget, bb, asking, ladder, delivery)

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

            # The three rewrites settle `run.text`, which every part reads
            # afterwards for its import prefix and its repair fallback.
            if graded_theorems(problem.challenge) > 1 and budget.can_ask():
                run.text = await self._share(problem, run.text, services, ledger, events)
            if definition_slots(run.text) and budget.can_ask():
                run.text = await self._define(problem, run.text, services, ledger, events)
            if names and budget.can_ask():
                run.text = await self._resolve_answers(
                    problem, run.text, names, services, ledger, events)

            bb.board = Board(run.text, bid=0)
            await bb.commit(await bb.look(run.text))
            tasks = [asyncio.ensure_future(loop.worker(m)) for m in run.cfg.lines]
            try:
                await asyncio.gather(*tasks)
            finally:
                loop.finished = True
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
            if run.loose:
                await asyncio.wait(list(run.loose))


def create_agent() -> BoardAgent:
    return BoardAgent()
