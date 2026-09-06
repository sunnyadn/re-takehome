"""One model call. Its pacing, its reasoning setting, and the Lean container
that is rotated while the call is in flight, because a call is the one moment
Lean is idle."""

from __future__ import annotations
import asyncio
import time
from typing import Any, Sequence

from re_harness import LLMCallError, Services

from submission.config import Config, FEEDBACK_CHARS, GOAL_CHARS, Ledger, RETRY_BACKOFF_S
from submission.contract import refused_before_generation, strip_fences
from submission.framework import insert_preamble
from submission.board.probes import container_memory_bytes
from submission.board.types import NARRATES
from submission.prompts import FRAMEWORK_SYSTEM, PLANNER_SYSTEM, sheet_for
from submission.replies import spoken, tool_lines
from re_harness import Problem
from submission.state import State


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


PLAN_TOKENS = 1500


class Caller:
    """How this run talks to its models: which lines it has, what a call costs
    it, and the two asks that are one call and a parse."""

    def __init__(self, config: Config) -> None:
        self.config = config
        # Per model: (completion tokens, seconds) of each reply, for `paced`.
        self._pace: dict[str, list[tuple[int, float]]] = {}

    def reasoning(self, model: str) -> dict[str, Any]:
        """Reasoning a model narrates in its content crowds out the step."""

        return NO_REASONING if any(n in model for n in NARRATES) else REASONING

    async def call(self, model: str, prompt: str, max_tokens: int, services: Services,
                    ledger: Ledger, system: str = "", think: bool = False,
                    tools: Sequence[Any] = ()) -> tuple[str, str]:
        """The reply and why the provider stopped, which is not always `stop`.

        Reasoning is off for steps because it crowds the block out of the reply.
        It stays on where thinking is the answer: the plan, and the arithmetic
        behind a numeric slot."""

        lean = getattr(services, "lean", None)
        if isinstance(lean, RenewingLean) and lean.due():
            lean.renew()
        max_tokens = self.paced(model, max_tokens)
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
                    reasoning=REASONING if think else self.reasoning(model),
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

    def paced(self, model: str, want: int) -> int:
        """`want` tokens, or what the slowest of the model's recent replies
        would produce inside LATENCY_BUDGET_S, whichever is less."""

        rates = [t / s for t, s in self._pace.get(model, [])[-PACE_WINDOW:]
                 if t >= PACE_MIN_TOKENS and s > 0]
        if len(rates) < 2:
            return want
        return max(PACE_FLOOR, min(want, int(min(rates) * LATENCY_BUDGET_S)))

    async def probe(self, state: State, block: str, services: Services) -> str:
        """A probe sits above the theorem, is read from its own check, and goes."""

        check = await services.lean.check_file(insert_preamble(state.text, block))
        printed = [str(m.get("data", "")).strip() for m in check.messages
                   if isinstance(m, dict) and m.get("severity") in ("info", "information")]
        return "\n".join(printed)[:FEEDBACK_CHARS] or "nothing"

    async def ask_plan(self, problem: Problem, state: State, services: Services,
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
        reply, _ = await self.call(model or self.config.lines[0], ask, PLAN_TOKENS,
                                    services, ledger, PLANNER_SYSTEM)
        return strip_fences(reply).strip()[:GOAL_CHARS]
