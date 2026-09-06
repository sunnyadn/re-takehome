"""Asking a question and reading the answer.

Two kinds of question: one to Lean (a probe file, a leaf block, a name scan)
and one to the other model (the audit). Both are paid for in the same currency
of wall clock and tokens, which is why this sits on `budget`. It reads the
board through `blackboard` but never makes one current; that is the caller's."""

from __future__ import annotations
import asyncio
import re
import time
from typing import Any, Sequence

from submission.config import FEEDBACK_CHARS
from submission.contract import format_messages
from submission.cells import enclosing, remap, render_check, reopen_past_cell
from submission.framework import (classify, hand_to_search, in_span, insert_preamble,
                                  message_line, prefixes, proof_span, root_names, unreachable)
from submission.framework_agent import RAISED_BUDGETS
from submission.prompts import notes_for
from submission.replies import BUDGET_RETRY
from submission.state import VACUOUS
from submission.techniques import blank_techniques, without_techniques
from submission.board.probes import (CHECK_TIMEOUT_FLOOR_S, audit_prompt, check_timeout_s,
                                     extract_file, goal_tokens, have_extract_file, is_closed,
                                     library_file, library_names, name_probe_file, read_library,
                                     read_name_probe, read_witness, statements, witness_file)
from submission.board.reply import ascribe_literals, claim_of, mine_statements
from submission.board.text import (enclosing_have, inflated, is_stated, put, split_statement,
                                   stated_facts)
from submission.board.types import (Board, Goal, HAVE_HEAD, binder_names, hyp_count,
                                    is_root_goal, narrates, owner, target_of)
from submission.run.blackboard import Blackboard
from submission.run.budget import Budget
from submission.run.context import Run

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
META = re.compile(r"\?[\w.]+|^(?:Type|Sort)\b")
AUDIT_TOKENS = 2500
# An auditor that has not answered by then lets the step through as unverified;
# the call runs on and is drained before the agent returns (a reservation left
# open fails the problem). Measured: one 482 s audit reply under the board lock.
AUDIT_WAIT_S = 120.0
AUDIT_SYSTEM = ("You audit one goal inside a Lean 4 proof. You answer with one "
                "JSON object and nothing else.")
INFLATION = 3.0


def _claimed_haves(base: Board, nxt: Board, lines: list[str]) -> list[dict[str, Any]]:
    """Every `have` in the file whose claim its declaration did not already
    state. Measured on putnam_2020_a2: a false `have` with a proof body had
    only its residue audited. The claim is audited whatever the body says."""

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
    return subjects


def _suspect_goals(nxt: Board, had: set[Any], lines: list[str],
                   covered: set[int]) -> list[dict[str, Any]]:
    """Goals the step left that a witness can decide on its own, minus the
    ones the board already had and the ones a `have` above already covers."""

    subjects: list[dict[str, Any]] = []
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
    return subjects


def _unchanged(goal: Goal, left: list[Goal]) -> str:
    if left and all(g.text == goal.text for g in left):
        return "that step left the goal exactly as it was"
    return ""


def _shadowed_name(goal: Goal, left: list[Goal]) -> str:
    if any(g.text.count("✝") > goal.text.count("✝") for g in left):
        # Measured on p10: `have h2 ...` accepted 18 times over, each one
        # shadowing the last, and the goal text never the same twice.
        return ("that step re-declared a name the context already "
                "has (Lean shows the old one as `h✝`); use the "
                "existing hypothesis instead of stating it again")
    return ""


def _false_from_nothing(goal: Goal, left: list[Goal]) -> str:
    if any(target_of(g.text) == "False" and target_of(goal.text) != "False"
           and hyp_count(g.text) <= hyp_count(goal.text) for g in left):
        # Measured on rmo_2001_2: a wrong witness left `hp : Nat.Prime 3,
        # hq : Nat.Prime 11 ⊢ False` and 14 turns went into it.
        return ("that step turned the goal into `False` without adding "
                "a hypothesis, so the context is still consistent and "
                "`False` cannot be proved: the witness, rewrite or case "
                "was wrong. Undo it and choose again")
    return ""


def _inflated_context(goal: Goal, left: list[Goal]) -> str:
    if left and max(inflated(goal.text, g.text) for g in left) >= INFLATION:
        # Measured on rmo_2001_2, p09 and rmo_2000_2 (5 runs): a rewrite
        # `at *` unfolded a variable in every hypothesis and both models
        # then worked on the unfolded form for the rest of the run.
        return ("that step made the existing hypotheses more than "
                f"{INFLATION:g}× larger without closing the goal (a rewrite "
                "unfolded a variable everywhere). Rewrite only the "
                "hypothesis you need, or state the fact you want as a `have`")
    return ""


def _uninferred_type(goal: Goal, left: list[Goal]) -> str:
    if any(META.search(target_of(g.text)) for g in left):
        # Measured on rmo_2000_2: `apply lt_irrefl _` left `⊢ Type ?u.350`
        # and `⊢ Preorder ?α`; each got a sorry and 30 turns, six deep.
        return ("that step left a goal Lean could not infer (`Type ?u`, "
                "`?α`): an `apply` with `_` for arguments it cannot fill. "
                "Give the term in full, e.g. `exact absurd h1 (not_lt.mpr h2)`")
    return ""


def _discarded_fact(goal: Goal, left: list[Goal]) -> str:
    if any(len(VACUOUS.findall(g.text)) > len(VACUOUS.findall(goal.text)) for g in left):
        # Measured on p09: `simp ... at h ⊢` left `h : True ⊢ False`, Lean
        # had no complaint, and five turns went into a goal that was dead.
        return ("that step turned a hypothesis into `True` (or `Type`), "
                "which throws the fact away; rewrite without `at h`, "
                "or use the fact instead of simplifying it")
    return ""


# Damage a step can do to the goals it leaves behind, in the order it is looked
# for. Lean raised no error on any of these: each one is a shape that a run was
# measured losing turns to.
COMPLAINTS = (_unchanged, _shadowed_name, _false_from_nothing,
              _inflated_context, _uninferred_type, _discarded_fact)


class Asking:
    def __init__(self, agent: Any, run: Run, budget: Budget, bb: Blackboard) -> None:
        self.agent, self.run, self.budget, self.bb = agent, run, budget, bb
        # The block-relative line of the first error, kept for the prefix cut,
        # and the span the last judged block occupied.
        self.failed_at = 0
        self.last_span = (0, 0)
        self.known_names: dict[str, str] = {}
        # The environment's answer to a goal's vocabulary, once per token set.
        self.shelf: dict[tuple[str, ...], str] = {}
        self.tried_statements: set[str] = set()
        self.audited: dict[tuple[str, str], str] = {}

    async def probe(self, text: str, line: int, timeout_s: int) -> tuple[list[dict[str, Any]], int]:
        """One check of the file with a probe line in it, focused on the cell
        or proof that holds the line; messages in file coordinates, and ms."""
        held = enclosing(text, line)
        focus: int | str | None = held.id if held else (owner(text, line) or None)
        rendered = render_check(text, self.run.cells, focus)
        check = await self.run.services.lean.check_file(blank_techniques(rendered.text), timeout_s=timeout_s)
        return remap(check.messages, rendered.lines), check.duration_ms

    async def nearest_names(self, messages: Sequence[dict[str, Any]], goal: Goal) -> str:
        """Lean's own answer to a misspelt library name, once per name."""
        names = library_names(messages, goal.text)
        fresh = [n for n in names if n not in self.known_names]
        if fresh and self.budget.affordable("scan"):
            imports = self.run.imports
            check = await self.run.services.lean.check_file(name_probe_file(imports, fresh), timeout_s=90)
            self.budget.spent("scan", check.duration_ms / 1000)
            found = read_name_probe(check.messages)
            for n in fresh:
                part = next((p for p in found.split("\n\n") if p.startswith(n + " ")), "")
                self.known_names[n] = part
            self.run.events.append({"stage": "names", "asked": fresh, "ms": check.duration_ms,
                           "found": bool(found)})
        return "\n".join(self.known_names[n] for n in names if self.known_names.get(n))

    async def consult(self, goal: Goal) -> None:
        """Ask the loaded Mathlib what it has for this goal's words, once."""
        tokens = tuple(goal_tokens(goal.text))
        if len(tokens) < 2:
            return
        if tokens not in self.shelf:
            if not self.budget.affordable("scan"):
                return
            imports = self.run.imports
            check = await self.run.services.lean.check_file(library_file(imports, tokens), timeout_s=90)
            self.budget.spent("scan", check.duration_ms / 1000)
            self.shelf[tokens] = read_library(check.messages)
            self.run.events.append({"stage": "library", "tokens": list(tokens),
                           "lines": self.shelf[tokens].count("\n") + bool(self.shelf[tokens]),
                           "ms": check.duration_ms})
        self.run.notes[goal.key].shelved = self.shelf[tokens]

    async def place(self, base: Board, goal: Goal, block: str) -> tuple[tuple[int, int], Board, bool]:
        """The block written at the goal, and the board that came back. A goal
        with a statement gets its own cell; one Lean will not elaborate on its
        own falls back to the enclosing cell. True when the step closed it."""

        splittable = goal.stmt and not self.run.notes[goal.key].unsplittable and not is_root_goal(base.text, goal)
        cell_id = self.run.cells.new(goal.stmt) if splittable else None
        focus: int | str = cell_id if cell_id is not None else (goal.cell or goal.decl)

        async def placed(trailing: bool) -> tuple[str, tuple[int, int], Board]:
            nonlocal cell_id, focus
            candidate, span = put(base.text, goal, block, trailing, cell_id)
            nxt = await self.bb.look(candidate, base, focus, goal)
            if cell_id is not None and any(message_line(m) == span[0] for m in classify(nxt.messages).failures):
                # The statement Lean printed does not elaborate on its own
                # (measured: a set literal loses its `: Set _`). A literal
                # is ascribed from the binder types once; failing that, the
                # block stays inside what encloses it and the goal is not
                # split again (measured on putnam_2018_a1: 128 such retries).
                repaired = ascribe_literals(goal.stmt)
                if repaired != goal.stmt and repaired not in self.tried_statements:
                    self.tried_statements.add(repaired)
                    self.run.cells.statements[cell_id] = repaired
                    nxt = await self.bb.look(candidate, base, focus, goal)
                if any(message_line(m) == span[0] for m in classify(nxt.messages).failures):
                    self.run.events.append({"stage": "inline", "cell": cell_id, "decl": goal.decl})
                    self.run.notes[goal.key].unsplittable = True
                    cell_id, focus = None, goal.cell or goal.decl
                    candidate, span = put(base.text, goal, block, trailing)
                    nxt = await self.bb.look(candidate, base, focus, goal)
                else:
                    self.run.notes[goal.key].known_stmt = repaired
            return candidate, span, nxt

        _, span, nxt = await placed(True)
        _, surplus, _, failures = classify(nxt.messages)
        if not failures and {message_line(m) for m in surplus if in_span(m, span)} == {span[1]}:
            # Only the trailing placeholder has no goal: the step closed it.
            _, span, nxt = await placed(False)
            return span, nxt, True
        return span, nxt, False

    async def judge_once(self, base: Board, goal: Goal, block: str) -> tuple[Board | None, str]:
        """The block is placed, then priced, then read for damage it did that
        Lean raised no error about. `failed_at` keeps the block-relative line
        of the first error, for the prefix cut."""

        span, nxt, closing = await self.place(base, goal, block)
        _, surplus, expensive, failures = classify(nxt.messages)
        self.last_span = span
        lines = [l for l in (message_line(m) for m in failures) if l and span[0] <= l <= span[1]]
        self.failed_at = (min(lines) - span[0]) if lines else 0
        if any("TIMEOUT" in str(m.get("data")) for m in failures):
            # Measured on putnam_2018_a1: a timed-out check cost 120s plus a
            # container restart, and the prefix cut then paid it again.
            return None, TIMED_OUT
        if expensive and not failures:
            return None, BUDGET_RETRY
        over_cap = nxt.ms > CHECK_CAP_MS and nxt.ms - base.ms > SLOW_STEP_MS // 5
        if self.bb.lenient or closing:
            # A closed goal is never re-elaborated by a later focused check;
            # only the comparator's cold compile pays it (measured on
            # rmo_2001_2: seven closing steps refused at 12-13 s from 0.2 s).
            over_cap = nxt.ms > LEAF_CAP_MS
        if not failures and ((nxt.ms - base.ms > SLOW_STEP_MS and not (self.bb.lenient or closing)) or over_cap):
            self.run.events.append({"stage": "slow", "ms": nxt.ms, "was": base.ms})
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
            names = await self.nearest_names(own, goal)
            return None, f"{said_text}\n{names}\n{notes_for(said_text)}".strip()
        lost = unreachable(nxt.messages, nxt.text, -1)
        if lost and lost[0] >= span[1]:
            # A goal outside the step's own lines that no placeholder reaches
            # (a `case` block took its sibling, the step closed the last hole
            # under a header report): it gets a placeholder where Lean says it
            # is, and the step stands. Measured on rmo_2000_6: the closing step
            # was refused for a goal it had not touched.
            reopened = await self.bb.look(reopen_past_cell(nxt.text, *lost), base)
            if not classify(reopened.messages).failures and not unreachable(reopened.messages, reopened.text, -1):
                self.run.events.append({"stage": "reopen", "line": lost[0], "decl": goal.decl})
                nxt, lost = reopened, None
        if lost:
            return None, ("that step left a goal open inside a branch nothing "
                          "can get back to. A step that splits the goal gives "
                          "every branch its own `sorry`, or closes it outright")
        if any(in_span(m, span) for m in surplus):
            return None, ("there are no goals left where that step was written: "
                          "the goal was already closed above it")
        left = [g for g in nxt.goals if span[0] <= g.line <= span[1]]
        for complaint in COMPLAINTS:
            why = complaint(goal, left)
            if why:
                return None, why
        return nxt, ""

    async def judge(self, base: Board, goal: Goal, block: str) -> tuple[Board | None, str]:
        """One edit at one goal, judged against the whole file; an edit that
        only ran out of Lean's budget is judged once more with the budget
        raised, whoever wrote it (a leaf as much as a model step)."""

        nxt, why = await self.judge_once(base, goal, block)
        if nxt is None and why == BUDGET_RETRY and RAISED_BUDGETS not in base.text:
            lifted = await self.bb.look(insert_preamble(base.text, RAISED_BUDGETS), base)
            moved = lifted.find(goal.key)
            if moved:
                self.run.events.append({"stage": "budget", "decl": goal.decl})
                nxt, why = await self.judge_once(lifted, moved, block)
        return nxt, why

    async def audit(self, author: str, base: Board, nxt: Board) -> str:
        """Every statement a step writes is tried against a witness: Lean
        states it, the auditor names values, Lean checks that they satisfy
        every hypothesis and break it. The refutation, or "" to let it in."""

        if not self.run.cfg.audit:
            return ""

        # Measured over 12 audits: a narrating model names values that violate
        # a hypothesis every time, at ~9 s; the other answers in ~1.4 s.
        other = next((m for m in self.run.cfg.lines if m != author and not narrates(m)),
                     next((m for m in self.run.cfg.lines if not narrates(m)),
                          next((m for m in self.run.cfg.lines if m != author), author)))
        lines = nxt.text.split("\n")
        subjects = _claimed_haves(base, nxt, lines)
        subjects += _suspect_goals(nxt, {g.key for g in base.goals}, lines,
                                   {s["at"] for s in subjects})
        for sub in subjects:
            if self.audited.get(sub["key"]):
                return self.audited[sub["key"]]
        subjects = [sub for sub in subjects if sub["key"] not in self.audited]
        if not subjects or not self.budget.can_ask():
            return ""
        goals = [sub for sub in subjects if "goal" in sub]
        haves = [sub for sub in subjects if "at" in sub]
        for sub in goals:
            sub["stmt"] = sub["goal"].stmt
        unstated = [sub for sub in goals if not sub["stmt"]]
        if unstated:
            said_ = statements((await self.probe(
                extract_file(nxt.text, [sub["goal"] for sub in unstated]),
                unstated[0]["goal"].line, check_timeout_s(nxt.ms)))[0])
            for sub in unstated:
                sub["stmt"] = said_.get(sub["goal"].line, "")
        if haves:
            text, where = have_extract_file(lines, [sub["at"] for sub in haves])
            said_ = statements((await self.probe(text, where.get(haves[0]["at"], 1), check_timeout_s(nxt.ms)))[0])
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
                sub["searched"], sub["found"] = await self.agent._enumerated(prefix, *sub["parsed"], self.run.services)
        # No binders, no question: the witness file alone decides a closed claim.
        # A claim the walk covered is settled: the auditor is asked about the rest.
        asked = [sub for sub in subjects
                 if sub["parsed"] and sub["parsed"][0] and not sub["found"] and not sub["searched"]]
        pending_calls = [asyncio.ensure_future(self.agent._call(
            other, audit_prompt(sub["stmt"], shown_prefix),
            AUDIT_TOKENS, self.run.services, self.run.ledger, system=AUDIT_SYSTEM)) for sub in asked]
        for t in pending_calls:
            self.run.loose.append(t)
            t.add_done_callback(lambda t: self.run.loose.remove(t) if t in self.run.loose else None)
        if pending_calls:
            done_calls, late = await asyncio.wait(pending_calls, timeout=AUDIT_WAIT_S)
            if late:
                self.run.events.append({"kind": "slow_call", "by": other, "audits": len(late),
                               "waited_s": AUDIT_WAIT_S})
        replies = [t.result() if t.done() else ("", "") for t in pending_calls]
        for sub in subjects:
            self.audited[sub["key"]] = ""
            reply, stopped = replies[asked.index(sub)] if sub in asked else ("", "")
            verdict, target, values = await self.decide(sub, reply, stopped, prefix)
            self.run.events.append({"kind": "audit",
                           "by": "evaluation" if sub.get("searched") else other,
                           "goal": target[:100], "verdict": verdict, "values": values})
            if verdict == "refuted":
                stmt = sub["what"] or f"⊢ {target}"
                if sub["claim"]:
                    self.bb.withdrawn.setdefault(sub["decl"], []).append(claim_of(sub["what"]))
                at = ", ".join(f"{n} = {v}" for n, v in values.items())
                self.audited[sub["key"]] = (
                    f"`{stmt}` is false, so the step was not posted: with {at} every "
                    "hypothesis in scope holds and it fails (Lean checked this). Do "
                    "not restate it; state a fact that is true at those values too"
                    if values else
                    f"that step left the goal `{stmt}`, which is false (Lean decided "
                    "it): the witness, rewrite or case was wrong. Undo it and choose again")
                return self.audited[sub["key"]]
        return ""

    async def decide(self, sub: dict[str, Any], reply: str, stopped: str,
                     prefix: str) -> tuple[str, str, dict[str, str]]:
        """What the evaluation walk, the auditor's reply and Lean together say
        about one claim: refuted with the values that break it, holds, or
        unverified. A claim Lean would not restate stays unstated."""

        verdict, values = "unstated", {}
        target = sub["claim"] or target_of(sub["goal"].text)
        if sub["parsed"]:
            groups, target = sub["parsed"]
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
                check = await self.run.services.lean.check_file(
                    witness_file(prefix, groups, values, target),
                    timeout_s=CHECK_TIMEOUT_FLOOR_S)
                if check.accepted:
                    verdict = "refuted"
        return verdict, target, values

    async def mine(self, base: Board, goal: Goal, block: str, author: str,
                   why: str) -> tuple[Board | None, str]:
        """The statements of a rejected block, posted as `sorry` facts at
        the goal. A statement Lean cannot elaborate or the audit refutes is
        dropped and the rest tried once more; the feedback stays the step's."""

        heads = mine_statements(block, stated_facts(base.text, goal.decl),
                                self.bb.withdrawn.get(goal.decl, []))
        if len(heads) < 2:
            return None, why
        for _ in range(2):
            skeleton = "\n".join(f"{h}\n  sorry" for h in heads)
            nxt, said_ = await self.judge(base, goal, skeleton)
            bad = await self.audit(author, base, nxt) if nxt is not None else ""
            if nxt is not None and not bad:
                self.run.events.append({"kind": "mined", "by": author, "facts": len(heads)})
                return nxt, ""
            if nxt is None:
                at = self.failed_at // 2 if self.failed_at else -1
                keep = [h for i, h in enumerate(heads) if i != at]
            else:
                keep = [h for h in heads if claim_of(h[:-len(" := by")]).strip() not in bad]
            if len(keep) < 2 or keep == heads:
                break
            heads = keep
        return None, why

    async def advance(self, base: Board, goal: Goal, block: str,
                      author: str) -> tuple[Board | None, str]:
        """A step, then its prefixes, then `exact?` in place of a bad proof."""

        opening = block.strip().split("\n")[0].strip()
        if opening and opening in self.bb.undone.get(goal.decl, []) and not opening.startswith("have "):
            # Measured on rmo_2000_6: a cell reset nine times, the model
            # re-writing the same opening step each time.
            return None, (f"`{opening[:80]}` was tried here and taken back after the goals "
                          "under it went nowhere; open with a different step")
        nxt, why = await self.judge(base, goal, block)
        if nxt is None and why not in (BUDGET_RETRY, TIMED_OUT) and not why.startswith(PARSE_FAULT):
            # The first error's line says where to cut; one check instead of
            # eight. Measured: 3.7 checks per model call, most of them here.
            cuts = prefixes(block)
            guided = [c for c in cuts if c.count("\n") + 1 <= max(self.failed_at, 1)]
            order = guided[:1] + [c for c in cuts if c not in guided[:1]]
            tried = 0
            while order and tried < 3:
                shorter = order[0]
                tried += 1
                nxt, _ = await self.judge(base, goal, shorter)
                if nxt is not None:
                    self.run.events.append({"kind": "prefix", "by": author,
                                   "lines": shorter.count("\n") + 1})
                    why = ""
                    break
                order = order[len(order) // 2 + 1:] if len(order) > 1 else []
            retry = hand_to_search(block)
            if nxt is None and retry != block and self.budget.affordable("retry"):
                # `exact?` costs ~27 s a call here and leaves 2 GB of index in
                # the container (measured, p10); it has a share of its own so
                # it cannot starve `apply?` on a stuck goal (measured on
                # rmo_2000_6: 9 retries used the scan share by 250 s and
                # `10 ≤ a * b` then waited 40 minutes for Nat.le_of_dvd).
                t0 = time.monotonic()
                nxt, _ = await self.judge(base, goal, retry)
                self.budget.spent("retry", time.monotonic() - t0)
                self.run.events.append({"kind": "search-retry", "by": author,
                               "accepted": nxt is not None})
            if nxt is None:
                nxt, why = await self.mine(base, goal, block, author, why)
        if nxt is None and why == BUDGET_RETRY:
            why = ("the step exceeded Lean's elaboration budget even at a "
                   "raised budget; make it cheaper")
        # Every board that leaves here is audited, whichever path accepted it.
        # Measured on rmo_2000_6: a prefix cut carried a false claim past it.
        if nxt is not None:
            bad = await self.audit(author, base, nxt)
            if bad:
                return None, bad
            return nxt, ""
        return nxt, why
