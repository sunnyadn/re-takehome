"""What `BoardAgent` inherits. One model call with its pacing and reasoning
settings, the plan and probe asks, and `_finish`, which takes the search back
out of a proved file. No loop lives here; the board's loop is in `run/loop.py`.
"""

from __future__ import annotations

import asyncio
import time
from typing import Any, Sequence

from re_harness import LLMCallError, Problem, Services

from submission.techniques import PREAMBLE_END
from submission.config import Config, FEEDBACK_CHARS, Ledger, RETRY_BACKOFF_S
from submission.contract import (declared_names, format_messages, refused_before_generation, strip_fences, suggested_tactics, suggestions)
from submission.framework import (statement_probes, alternatives, declaration_name,
                                  graded_theorems, answer_slots, collapse, first_blocks,
                                  have_spans, classify, cursor_goal, drop_lines, fill_answer,
                                  insert_preamble, is_done, as_goal,
                                  placeholders, render)
from submission.prompts import FRAMEWORK_SYSTEM, PLANNER_SYSTEM, sheet_for
from submission.replies import lighter_forms, printed_numbers, spoken, tool_lines
from submission.state import State

# The ceiling for a step from the narrating line only; the other line gets
# `board/types.py::SLOW_STEP_TOKENS`, and `step_tokens` chooses. 2000 was too
# few either way (measured on p08: gpt-oss-120b spent all 2000 reasoning and
# returned `content: None` with `finish_reason: length`).
STEP_TOKENS = 6000
ANSWER_TOKENS = 4000
# Measured on p09: qwen3.5-flash narrates its reasoning as ordinary content and
# the code block after it is what the token limit cuts. Over three samples each,
# reasoning off halves the reply and every one of them begins with the block.
# gpt-oss-120b answers HTTP 400 rather than turn it off, and that 400 is fatal:
# the ledger marks accounting incomplete and never clears it, so the next call
# aborts the problem. The setting is therefore decided by name, never probed.
REASONING = {"effort": "low"}
# The harness reads a reply for at most 180 s and a ReadTimeout leaves the
# ledger unknown, which scores the problem 0 whatever the file says. Measured
# on p10 (v7.79): a 4000-token step call at 19 tokens/s ran 206 s and zeroed a
# proof that had been accepted 38 s earlier. So a call may ask for no more
# tokens than the slowest recent reply rate produces in LATENCY_BUDGET_S.
LATENCY_BUDGET_S = 120.0
PACE_WINDOW = 6
PACE_MIN_TOKENS = 400
PACE_FLOOR = 1200
NO_REASONING = {"enabled": False}
NARRATES = ("qwen",)
GOAL_CHARS = 4000
FILE_CHARS = 8000
PLAN_TOKENS = 1500

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
LOOSE_DRAIN_S = 30.0
MAX_DELETIONS = 12
# Each try is one check, and a check is 60ms against a reply's seconds.
MAX_PREFIXES = 8
FINISH_RESERVE_S = 300.0
# Lean's budgets are deterministic, so raising them is sound; it buys that
# determinism with wall clock, which the comparator caps at 180s. Measured on
# p06_pow_mod: what a large power needs is recursion depth, not heartbeats.
RAISED_BUDGETS = ("set_option maxHeartbeats 400000\n"
                     "set_option maxRecDepth 8000\n"
                     "set_option exponentiation.threshold 4000")
# The comparator allows 180 seconds, so a file that only just compiles here is
# not safe there. Recorded, never silently accepted.
SLOW_COMPILE_MS = 150_000

class FrameworkAgent:
    def __init__(self, config: Config | None = None):
        self.config = config or Config.from_env()
        # Per model: (completion tokens, seconds) of each reply, for _paced.
        self._pace: dict[str, list[tuple[int, float]]] = {}

    def _reasoning(self, model: str) -> dict[str, Any]:
        """Reasoning a model narrates in its content crowds out the step."""

        return NO_REASONING if any(n in model for n in NARRATES) else REASONING

    async def _look(self, text: str, services: Services, focus: int = 0) -> State:
        """One check does both jobs: it adjudicates, and it prints the next goal."""

        open_goals = len(placeholders(text))
        focus = min(max(focus, 0), open_goals - 1) if open_goals else 0
        source, line = render(text, focus)
        check = await services.lean.check_file(source)
        return State(text=text, goal=cursor_goal(check.messages, line), line=line,
                     messages=list(check.messages), accepted=check.accepted,
                     focus=focus, goals=open_goals)

    async def _finish(self, state: State, services: Services, time_left) -> State:
        """Take the search out of a finished file: the comparator allows 180s."""

        state = await self._substitute_search(state, services)
        # Measured on p08: both passes turned a file the comparator accepted
        # into one it timed out on, because deleting a fact a closer was using
        # makes that closer redo the work in a term the kernel then re-checks.
        # A short file has nothing to win here, and §4 says not to touch it.
        if len(below_header(state.text)) > TIDY_ABOVE_BYTES:
            state = await self._lighten(state, services, time_left)
            state = await self._prune(state, services, time_left)
        for _ in range(MAX_COLLAPSE):
            blocks = first_blocks(state.text)
            if not blocks or time_left() < FINISH_RESERVE_S:
                break
            collapsed = None
            for tactic in alternatives(blocks[0].group(2)):
                probe = await self._look(collapse(state.text, blocks[0], tactic), services)
                if probe.accepted:
                    collapsed = probe
                    break
            if collapsed is None:
                break
            state = collapsed
        return state

    async def _lighten(self, state: State, services: Services, time_left) -> State:
        """Make the finished term small.

        Measured on p08: `nlinarith` with three hints checks in 348ms here and
        times out at the comparator's 180s, with one hint it passes."""

        for rewrite in lighter_forms(state.text)[:MAX_LIGHTEN]:
            if time_left() < FINISH_RESERVE_S:
                break
            probe = await self._look(rewrite, services)
            if probe.accepted and is_done(probe.text):
                state = probe
        return state

    async def _prune(self, state: State, services: Services, time_left) -> State:
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
            probe = await self._look(
                drop_lines(state.text, range(start, end + 1)), services)
            if probe.accepted and is_done(probe.text):
                state = probe
        return state

    async def _substitute_search(self, state: State, services: Services) -> State:
        """Replace each `exact?` with the term it printed, keeping the search
        call when the term does not re-elaborate."""

        if "exact?" not in state.text and "apply?" not in state.text:
            return state
        for term in suggested_tactics(suggestions(state.messages))[:4]:
            probe = await self._look(state.text.replace("exact?", term, 1), services)
            if probe.accepted:
                return probe
        return state

    async def _probe(self, state: State, block: str, services: Services) -> str:
        """A probe sits above the theorem, is read from its own check, and goes."""

        check = await services.lean.check_file(insert_preamble(state.text, block))
        printed = [str(m.get("data", "")).strip() for m in check.messages
                   if isinstance(m, dict) and m.get("severity") in ("info", "information")]
        return "\n".join(printed)[:FEEDBACK_CHARS] or "nothing"

    async def _ask_plan(self, problem: Problem, state: State, services: Services,
                        ledger: Ledger, model: str = "", avoid: Sequence[str] = ()) -> str:
        """The mathematics, from the model that answers in mathematics. Routes
        already tried on this declaration are named so the next one differs."""

        ask = (f"Problem: {problem.description}\n\nThe goal, as Lean reports it:\n"
               f"{state.goal[:GOAL_CHARS]}\n\nHow do you prove this?")
        sheet = sheet_for(state.goal)
        if sheet:
            # The route hints on the sheets (squeeze between powers, prime
            # dividing a factor, block the sum) are for the planner as much as
            # for the writer; the names tell it what Mathlib can do in one step.
            ask += f"\n\nWhat the loaded Mathlib has for this goal's vocabulary:\n{sheet}"
        if avoid:
            tried = "\n".join(f"- {a[:300]}" for a in list(avoid)[-3:])
            ask += ("\n\nRoutes already tried on this goal that did not work out. "
                    f"Give a different one:\n{tried}")
        # Measured on p10: with reasoning on, the plan came back as "The user is
        # asking me to prove a theorem in Lean 4", which costs a call and enters
        # every later prompt. Reasoning stays on only where it is the answer.
        reply, _ = await self._call(model or self.config.lines[0], ask, PLAN_TOKENS,
                                    services, ledger, PLANNER_SYSTEM)
        return strip_fences(reply).strip()[:GOAL_CHARS]

    async def _share(self, problem: Problem, text: str, services: Services,
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
            self._call(line, ask, STEP_TOKENS, services, ledger,
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
            reply, _ = await self._call(
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

    async def _call(self, model: str, prompt: str, max_tokens: int, services: Services,
                    ledger: Ledger, system: str = "", think: bool = False,
                    tools: Sequence[Any] = ()) -> tuple[str, str]:
        """The reply and why the provider stopped, which is not always `stop`.

        Reasoning is off for steps because it crowds the block out of the reply.
        It stays on where thinking is the answer: the plan, and the arithmetic
        behind a numeric slot."""

        max_tokens = self._paced(model, max_tokens)
        for wait in (0.0,) + RETRY_BACKOFF_S:
            if wait:
                await asyncio.sleep(wait)
            started = time.monotonic()
            try:
                reply = await services.llm.complete(
                    model=model,
                    messages=[{"role": "system", "content": system or FRAMEWORK_SYSTEM},
                              {"role": "user", "content": prompt}],
                    max_tokens=max_tokens,
                    temperature=0.4,
                    reasoning=REASONING if think else self._reasoning(model),
                    **({"tools": list(tools),
                        "tool_choice": {"type": "function",
                                        "function": {"name": "answer"}}} if tools else {}),
                )
            except LLMCallError as exc:
                if refused_before_generation(exc):
                    continue
                raise
            ledger.record(reply.usage)
            self._pace.setdefault(model, []).append(
                (int((reply.usage or {}).get("completion_tokens") or 0), time.monotonic() - started))
            said = tool_lines(reply.tool_calls) or spoken(reply.content or "")
            return said, reply.finish_reason or ""
        return "", ""

    def _paced(self, model: str, want: int) -> int:
        """`want` tokens, or what the slowest of the model's recent replies
        would produce inside LATENCY_BUDGET_S, whichever is less."""

        rates = [t / s for t, s in self._pace.get(model, [])[-PACE_WINDOW:]
                 if t >= PACE_MIN_TOKENS and s > 0]
        if len(rates) < 2:
            return want
        return max(PACE_FLOOR, min(want, int(min(rates) * LATENCY_BUDGET_S)))

