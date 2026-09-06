"""A board of open goals, two models working two of them at once, Lean judging
every edit against the whole file. `solve` below is the spine: it wires the
seven parts of `submission/run/`, and what it borrows sits in the class below."""


from __future__ import annotations

import asyncio
import re
import time
from typing import Any, Sequence

from re_harness import AgentResult, LLMCallError, Problem, Services
from re_harness.budget import BudgetAccountingError, BudgetExceeded
from re_harness.lean import LeanRuntimeError

from submission.sampling import read_sample_hit, sample_file, sampled_search
from submission.techniques import without_techniques
from submission.config import FEEDBACK_CHARS, Ledger
from submission.contract import format_messages, in_file_coordinates, scoring_faults
from submission.sweep import split_files, sweep_files, usable_cocktail
from submission.framework import (classify, definition_slots, fill_definition, graded_theorems, line_of, placeholders, proof_span, root_names)
from submission.contract import strip_fences
from submission.framework_agent import ANSWER_TOKENS, FILE_CHARS, FrameworkAgent, LOOSE_DRAIN_S
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
from submission.board.probes import (CHECK_TIMEOUT_FLOOR_S, audit_prompt, container_memory_bytes, counterexample_search, extract_file, read_witness, read_witnesses, searched_clean, statements, witness_file, witness_search_file)


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
    """The board program. It overrides `_share` and `_call`, adds `_define` and
    `solve`, and borrows `_ask_plan`, `_probe`, `_resolve_answers` and `_finish`
    from `FrameworkAgent` unchanged."""

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
        ledger, names = run.ledger, run.names
        budget = Budget(run)
        delivery = Delivery(self, run, budget)
        bb = Blackboard(run, budget, delivery)
        asking = Asking(self, run, budget, bb)
        ladder = Ladder(run, budget, bb, asking)
        loop = Loop(self, run, budget, bb, asking, ladder, delivery)

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
