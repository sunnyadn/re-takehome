"""Two lines of attack, one per model, arbitrated by the Lean compiler.

Round 1 measured the two models solving overlapping but different problems: the
union of what either could solve was worth three more points than the better of
the two alone, and a fixed plan/formalise/repair pipeline captured none of it.
So this agent stops assigning roles by model and instead runs one independent
line of attack per model, interleaved under a shared clock. Whichever line the
compiler accepts first wins.

The collaboration proper is one rule on top: when a line stops making progress,
measured by its Lean error signature not moving, the other model takes the next
turn on that line, inheriting its candidate and its plan.
"""

from __future__ import annotations

import asyncio
import os
import re
import time
from dataclasses import dataclass, field
from typing import Any, Sequence

from re_harness import AgentResult, LLMCallError, Problem, Services
from re_harness.budget import BudgetAccountingError, BudgetExceeded
from re_harness.llm import REFUSED_BEFORE_GENERATION
from re_harness.config import HarnessSettings
from re_harness.lean import numeric_answers_are_literals
from re_harness.models import ALLOWED_MODELS, MODEL_A, MODEL_B

# A refused call releases its reservation, so repeating it is free and the
# problem stays winnable. Without this a single 429 ends the problem.
RETRY_BACKOFF_S = (5.0, 20.0, 60.0)
# budget.release_unbilled keeps each refused call's reservation as worst-case
# exposure for the rest of the problem, and the ledger closes when that
# exposure crosses the limit. Measured: 48 refusals do it at 8 hours.
MAX_RETRIES_PER_PROBLEM = 8
PLAN_TOKENS = 16000
FORMALIZE_TOKENS = 16000
REPAIR_TOKENS = 16000
FEEDBACK_CHARS = 6000


def _env_models(name: str, default: Sequence[str]) -> tuple[str, ...]:
    raw = os.environ.get(name, "").strip()
    if not raw:
        return tuple(default)
    models = tuple(part.strip() for part in raw.split(",") if part.strip())
    if not models or any(m not in ALLOWED_MODELS for m in models):
        raise ValueError(f"{name} must be a comma-separated list of {sorted(ALLOWED_MODELS)}")
    return models


@dataclass(frozen=True)
class Config:
    """Which models get a line. One model listed twice is the solo control."""

    lines: tuple[str, ...] = (MODEL_A, MODEL_B)
    # A runaway backstop, not the intended stop. Round 2 ended every run on
    # this cap while using about an eighth of the clock and the money, so it
    # is set past anything the deadline and budget can actually allow.
    max_turns_per_line: int = 500
    stall_before_handoff: int = 1
    budget_usd: float = 1.00
    time_limit_s: float = 28800.0
    # The worker hands the agent time_limit minus this, then hard-cancels.
    verify_reserve_s: float = 120.0
    # A turn started inside this window can be killed mid-call, and a cancelled
    # call closes the ledger, which scores the problem zero however good the
    # checkpoint is. Sized as a share of the limit, because a fixed margin from
    # the slowest call seen so far was beaten by 2.4x the first time it ran.
    stop_margin_floor_s: float = 900.0
    stop_margin_fraction: float = 0.1

    @classmethod
    def from_env(cls) -> "Config":
        settings = HarnessSettings.from_env(n_workers=1)
        return cls(
            lines=_env_models("VM_LINES", (MODEL_A, MODEL_B)),
            budget_usd=settings.budget_usd,
            time_limit_s=settings.time_limit_s,
            verify_reserve_s=float(settings.verify_reserve_s),
        )

    @property
    def agent_deadline_s(self) -> float:
        """Mirror of the worker's own deadline arithmetic."""

        reserve = min(self.verify_reserve_s, self.time_limit_s * 0.25)
        return max(60.0, self.time_limit_s - reserve)

    @property
    def stop_margin_s(self) -> float:
        """Wide enough for a turn already in flight, never a quarter of the run.

        Without the cap the 8-hour floor swallowed 47% of a 30-minute run."""

        want = max(self.stop_margin_floor_s, self.stop_margin_fraction * self.time_limit_s)
        return min(want, 0.25 * self.time_limit_s)

    @property
    def last_turn_start_s(self) -> float:
        """No turn may start after this, so none is in flight at the cancel."""

        deadline = self.agent_deadline_s
        return max(30.0, deadline - min(self.stop_margin_s, deadline * 0.5))


@dataclass
class Line:
    """One model's independent attempt at the problem."""

    index: int
    owner: str
    plan: str = ""
    candidate: str = ""
    errors: int | None = None
    signature: str | None = None
    stalls: int = 0
    feedback: str = ""
    done: bool = False

@dataclass
class Ledger:
    """Local mirror of spend, which Services does not expose, plus a turn log."""

    spent_usd: float = 0.0
    events: list[dict[str, Any]] = field(default_factory=list)

    def record(self, usage: Any) -> float:
        # llm.complete validates usage.cost before returning, so this is total.
        cost = float(usage["cost"])
        self.spent_usd += cost
        return cost


def normalise_imports(source: str, fallback: str) -> str:
    """Force a single `import Mathlib` header.

    The REPL strips imports and checks against a full Mathlib environment, while
    the Comparator compiles the real file. Widening the imports closes that gap,
    and a direct Comparator run confirmed a widened solution is still accepted.
    """

    body = "\n".join(
        line for line in source.splitlines() if not line.lstrip().startswith("import ")
    ).strip()
    if not body:
        return fallback
    return "import Mathlib\n\n" + body + "\n"


def extract_lean(text: str, fallback: str) -> str:
    fenced = re.findall(r"```(?:lean|lean4)?\s*\n(.*?)```", text, flags=re.DOTALL | re.IGNORECASE)
    for block in reversed(fenced):
        if block.strip():
            return normalise_imports(block, fallback)
    stripped = text.strip()
    if "import " in stripped or "theorem " in stripped:
        return normalise_imports(stripped, fallback)
    return fallback


BANNED = re.compile(r"\b(sorry|sorryAx|admit|native_decide|unsafe)\b|^\s*axiom\s", re.MULTILINE)
ANSWER_SLOT = re.compile(r"^\s*abbrev\s+([A-Za-z_][\w']*)\s*:\s*\u2115\s*:=", re.MULTILINE)
DECL = re.compile(r"^\s*(?:theorem|lemma|abbrev|def)\s+([A-Za-z_][\w']*)", re.MULTILINE)
AXIOM_LINE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
PERMITTED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})


def banned_constructs(source: str) -> list[str]:
    """The Comparator permits only propext, Classical.choice and Quot.sound, so
    these compile against the REPL and still score zero."""

    return sorted({m.group(0).strip() for m in BANNED.finditer(source)})


def declared_names(challenge: str) -> tuple[str, ...]:
    """Every declaration the Comparator will look at."""

    return tuple(dict.fromkeys(DECL.findall(challenge)))


def statement_headers(source: str) -> dict[str, str]:
    """Each declaration's text up to its `:=`, whitespace normalised.

    The Comparator requires kernel-level statement equality per declared name,
    so any edit to a header scores zero however well the proof compiles."""

    headers: dict[str, str] = {}
    name = None
    buffer: list[str] = []
    for line in source.splitlines():
        match = DECL.match(line)
        if match:
            if name and name not in headers:
                headers[name] = " ".join(" ".join(buffer).split())
            name, buffer = match.group(1), []
        if name is None or line.lstrip().startswith("--"):
            continue
        head, sep, _rest = line.partition(":=")
        buffer.append(head)
        if sep:
            headers[name] = " ".join(" ".join(buffer).split())
            name, buffer = None, []
    return headers


def statement_drift(challenge: str, candidate: str) -> list[str]:
    """Names the candidate dropped or reworded."""

    original = statement_headers(challenge)
    now = statement_headers(candidate)
    faults = []
    for name, header in original.items():
        if name not in now:
            faults.append(f"{name} is missing, the grader needs it byte-identical")
        elif now[name] != header:
            faults.append(f"{name} was reworded, restore it exactly as the challenge has it")
    return faults


def forbidden_axioms(messages: Sequence[dict[str, Any]]) -> list[str]:
    """Read `#print axioms` output. A denylist cannot work here, because
    `native_decide` and `bv_decide` mint a fresh axiom name per computation."""

    bad: set[str] = set()
    for m in messages:
        for _decl, axioms in AXIOM_LINE.findall(str(m.get("data", ""))):
            bad |= {a.strip() for a in axioms.split(",") if a.strip()} - PERMITTED_AXIOMS
    return sorted(bad)


def answer_names(challenge: str) -> tuple[str, ...]:
    """Nat answer slots, which must end up as plain decimal literals."""

    return tuple(ANSWER_SLOT.findall(challenge))


def scoring_faults(source: str, names: Sequence[str], challenge: str = "") -> list[str]:
    """What the Comparator would reject even though Lean accepted the file."""

    faults = [f"remove {c}, the grader rejects it" for c in banned_constructs(source)]
    if challenge:
        faults.extend(statement_drift(challenge, source))
    if names:
        _, errors = numeric_answers_are_literals(source, tuple(names))
        faults.extend(errors)
    return faults


# Generic tactic library. RULES.md allows these explicitly, and `first`
# backtracks between alternatives, so the whole cocktail costs one Lean check.
COCKTAIL = (
    "rfl", "trivial", "norm_num", "simp", "omega", "positivity", "ring",
    "linarith", "nlinarith", "field_simp; ring", "simp; omega",
    "norm_num; omega", "constructor <;> norm_num", "simp_all", "aesop",
    "decide", "norm_num [Nat.factorial]", "gcongr", "bound", "norm_cast",
    "push_cast; ring", "interval_cases <;> norm_num", "exact le_refl _",
    "tauto", "subst_vars <;> omega", "constructor <;> omega",
    "refine ⟨?_, ?_⟩ <;> norm_num", "simp_all <;> omega", "zify; omega",
    "push_cast; omega", "ring_nf; omega", "ring_nf; nlinarith",
    "norm_num [Nat.Prime]", "interval_cases <;> omega",
    "simp_arith", "constructor <;> simp", "refine ⟨?_, ?_, ?_⟩ <;> norm_num",
    "norm_num [Nat.pow_mod]", "simp [Nat.pow_mod]; omega", "norm_num [Nat.gcd]",
    "norm_num [Nat.choose]", "norm_num [Nat.ModEq]", "decide <;> norm_num",
    "simp [Finset.sum_range_succ]; ring", "simp [Finset.sum_range_succ]; norm_num",
    "simp [Nat.div_add_mod]; omega", "field_simp; nlinarith", "rify; nlinarith",
    "norm_num [Nat.factorial]; ring", "omega <;> norm_num",
)
PREAMBLES = (
    "",
    "set_option maxRecDepth 8000 in\n",
    "set_option exponentiation.threshold 4000 in\nset_option maxRecDepth 8000 in\n",
)
PROOF_DECL = re.compile(r"^\s*(theorem|lemma)\s")
DECL_START = re.compile(r"^\s*(theorem|lemma|abbrev|def|example)\s")


def splice_tactic(source: str, tactic: str) -> tuple[str, int, int]:
    """Put one tactic block into every theorem body.

    Returns the new source, how many bodies were filled, and how many `sorry`
    placeholders survive elsewhere (an unfilled answer slot, say)."""

    filled = left = 0
    out: list[str] = []
    in_proof = False
    for line in source.splitlines():
        if DECL_START.match(line):
            in_proof = bool(PROOF_DECL.match(line))
        stripped = line.strip()
        indent = line[: len(line) - len(stripped)]
        if in_proof and stripped == "sorry":
            out.append(f"{indent}{tactic}")
            filled += 1
            continue
        if in_proof and stripped.endswith(":= sorry"):
            out.append(line.rstrip()[: -len("sorry")] + f"by\n{indent}  {tactic}")
            filled += 1
            continue
        if "sorry" in stripped:
            left += 1
        out.append(line)
    return "\n".join(out) + "\n", filled, left


def wrap_tactic(tactic: str) -> str:
    """`first` takes the first alternative that does not fail, and tactics like
    `norm_num` succeed by rewriting without closing the goal, which would stop
    the search early. `done` turns those into failures so the search continues."""

    return f"({tactic}; done)"


async def usable_cocktail(services: Services) -> tuple[str, ...]:
    """Drop tactics this Mathlib does not know.

    One unknown name makes the whole `first` block fail to elaborate, so a
    cocktail that is not version-checked can silently stop working."""

    usable = []
    for tactic in COCKTAIL:
        probe = f"theorem vm_probe : True := by\n  first\n    | {wrap_tactic(tactic)}\n    | trivial"
        check = await services.lean.check_file(probe)
        if not any("unknown tactic" in str(m.get("data", "")) for m in check.messages):
            usable.append(tactic)
    return tuple(usable)


def sweep_files(source: str, cocktail: Sequence[str] = COCKTAIL) -> list[str]:
    """Deterministic candidates to try before spending a token on the models.

    Empty when a `sorry` survives outside the theorem bodies, since Lean can
    never accept that file however good the proof is."""

    # A bare `;` inside an alternative truncates the whole `first` block, so
    # every multi-tactic alternative is parenthesised.
    alternation = "first\n" + "\n".join(f"    | {wrap_tactic(t)}" for t in cocktail)
    files: list[str] = []
    for preamble in PREAMBLES:
        body, filled, left = splice_tactic(source, alternation)
        if not filled or left:
            return []
        files.append(normalise_imports(preamble + body, body))
    return files


IMPORT_LINE = re.compile(r"^\s*import\s")
NO_GOALS = "no goals to be solved"


def surplus_lines(messages: Sequence[dict[str, Any]], source: str) -> list[int]:
    """Source lines holding a tactic that ran after its goal was already closed.

    Lean strips import lines before elaborating, so a reported position is
    offset by the number of imports above it."""

    kept = [i for i, l in enumerate(source.splitlines(), start=1) if not IMPORT_LINE.match(l)]
    out = set()
    for m in messages:
        if m.get("severity") != "error" or NO_GOALS not in str(m.get("data", "")).lower():
            continue
        reported = (m.get("pos") or {}).get("line")
        if reported and 1 <= int(reported) <= len(kept):
            out.add(kept[int(reported) - 1])
    return sorted(out)


def drop_lines(source: str, drop: Sequence[int]) -> str:
    removed = set(drop)
    kept = [l for i, l in enumerate(source.splitlines(), start=1) if i not in removed]
    return "\n".join(kept) + "\n"


def error_messages(messages: Sequence[dict[str, Any]]) -> list[str]:
    return [
        str(m.get("data", "")).strip()
        for m in messages
        if m.get("severity") == "error"
    ]


def error_signature(messages: Sequence[dict[str, Any]]) -> str:
    """Compared only for equality, so the joined first lines are the identity."""

    return "\n".join(sorted(m.splitlines()[0][:200] for m in error_messages(messages) if m))


def format_messages(messages: Sequence[dict[str, Any]]) -> str:
    """Keep the earliest diagnostics, since later ones usually cascade."""

    chunks = [
        f"{m.get('severity')} at {m.get('pos')}: {str(m.get('data', '')).strip()}"
        for m in messages
        if m.get("severity") in ("error", "warning")
    ]
    return "\n\n".join(chunks)[:FEEDBACK_CHARS] if chunks else ""


class SubmissionAgent:
    def __init__(self, config: Config | None = None):
        self._deadline: float | None = None
        self._retries_left = MAX_RETRIES_PER_PROBLEM
        self.config = config or Config.from_env()

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        cfg = self.config
        started = time.monotonic()
        deadline = started + cfg.last_turn_start_s
        self._deadline = deadline
        self._retries_left = MAX_RETRIES_PER_PROBLEM
        ledger = Ledger()
        names = answer_names(problem.challenge)
        decls = declared_names(problem.challenge)
        lines = [Line(index=i, owner=m) for i, m in enumerate(cfg.lines)]
        best = normalise_imports(problem.challenge, problem.challenge)
        best_rank = (False, -(10**9))
        winner: int | None = None

        def time_left() -> float:
            return deadline - time.monotonic()

        def offer(line: Line, accepted: bool) -> bool:
            """Checkpoint this candidate when it outranks the incumbent."""

            nonlocal best, best_rank, winner
            if not line.candidate or line.errors is None:
                return False
            rank = (accepted, -line.errors)
            if rank <= best_rank:
                return False
            best, best_rank = line.candidate, rank
            if accepted:
                winner = line.index
            services.checkpoint(
                best, {"line": line.index, "errors": line.errors, "accepted": accepted}
            )
            return True

        try:
            # Free points first. The tactic library is deterministic and costs
            # no tokens, so it runs before any model is asked anything.
            for candidate in sweep_files(problem.challenge, await usable_cocktail(services)):
                if time_left() <= 0:
                    break
                check = await services.lean.check_file(candidate)
                if check.accepted and not scoring_faults(candidate, names, problem.challenge):
                    ledger.events.append({"stage": "sweep", "accepted": True})
                    services.checkpoint(candidate, {"stage": "sweep"})
                    return AgentResult(candidate, {
                        "lines": list(cfg.lines), "winner_line": None,
                        "solved_by": "deterministic_sweep",
                        "accepted_by_repl": True, "spend_usd": 0.0,
                        "wall_s": round(time.monotonic() - started, 1),
                        "events": ledger.events,
                    })
            for _ in range(cfg.max_turns_per_line):
                if winner is not None or all(l.done for l in lines) or time_left() <= 0:
                    break
                for line in lines:
                    if line.done or time_left() <= 0:
                        continue
                    accepted = await self._advance(problem, line, services, ledger, names, decls)
                    offer(line, accepted)
                    if winner is not None:
                        break
        except (LLMCallError, BudgetAccountingError) as exc:
            # The problem's ledger is closed, so no further call can succeed on
            # any line. Keep the best candidate and stop.
            ledger.events.append({"stage": "stop", "note": f"{type(exc).__name__}: {exc}"[:300]})

        return AgentResult(
            best,
            {
                "lines": list(cfg.lines),
                "winner_line": winner,
                "accepted_by_repl": winner is not None,
                "spend_usd": round(ledger.spent_usd, 6),
                "wall_s": round(time.monotonic() - started, 1),
                "events": ledger.events,
            },
        )

    async def _advance(
        self, problem: Problem, line: Line, services: Services, ledger: Ledger,
        names: Sequence[str], decls: Sequence[str],
    ) -> bool:
        """Take one turn on this line. Returns True if Lean accepted it."""

        cfg = self.config
        # A stalled line is handed to the other model, carrying its own context.
        other = next((m for m in cfg.lines if m != line.owner), None)
        handoff = line.stalls > cfg.stall_before_handoff and other is not None
        model = other if handoff else line.owner

        if not line.candidate:
            plan = await self._call(
                model, PLANNER_SYSTEM, planner_user(problem), PLAN_TOKENS,
                services, ledger, line.index, "plan", handoff,
            )
            if plan is None:
                line.done = True
                return False
            line.plan = plan
            content = await self._call(
                model, FORMALIZER_SYSTEM, formalizer_user(problem, line.plan), FORMALIZE_TOKENS,
                services, ledger, line.index, "formalize", handoff,
            )
        else:
            content = await self._call(
                model, REPAIRER_SYSTEM, repairer_user(problem, line, handoff), REPAIR_TOKENS,
                services, ledger, line.index, "repair", handoff,
            )
        if content is None:
            line.done = True
            return False

        previous = line.candidate
        line.candidate = extract_lean(content, fallback=previous or problem.challenge)
        if line.candidate == previous:
            # Nothing changed, so the verdict cannot change either. Count it as
            # a stall rather than paying for an identical Lean check.
            line.stalls += 1
            return False

        probe = "\n".join(f"#print axioms {n}" for n in decls)
        suffix = "\n\n" + probe if probe else ""
        check = await services.lean.check_file(line.candidate + suffix)
        # A tactic that reports `no goals` is surplus: the step before it already
        # closed the goal. Dropping it costs one Lean check and no tokens.
        surplus = [] if check.accepted else surplus_lines(check.messages, line.candidate)
        if surplus:
            mended = drop_lines(line.candidate, surplus)
            recheck = await services.lean.check_file(mended + suffix)
            if recheck.accepted and not scoring_faults(mended, names, problem.challenge):
                ledger.events.append({"line": line.index, "stage": "drop_surplus",
                                      "lines": surplus, "accepted": True})
                line.candidate, check = mended, recheck
        faults = scoring_faults(line.candidate, names, problem.challenge)
        faults += [f"{a} is not a permitted axiom, the grader rejects it"
                   for a in forbidden_axioms(check.messages)]
        signature = "\n".join([error_signature(check.messages)] + faults)
        line.errors = len(error_messages(check.messages)) + len(faults)
        line.stalls = line.stalls + 1 if signature == line.signature else 0
        line.signature = signature
        line.feedback = "\n".join(faults + [format_messages(check.messages)]).strip() or (
            "Lean timed out. Use cheaper tactics and avoid decide or norm_num on large numbers."
            if check.timed_out else ""
        )
        # Lean accepting the file is not the grading condition.
        accepted = check.accepted and not faults
        ledger.events.append({
            "line": line.index, "stage": "lean_check", "model": model,
            "errors": line.errors, "accepted": check.accepted, "handoff": handoff,
            "timed_out": check.timed_out, "scoring_faults": faults,
        })
        return accepted

    def _time_left(self) -> float:
        return float("inf") if self._deadline is None else self._deadline - time.monotonic()

    async def _call(
        self, model: str, system: str, user: str, max_tokens: int,
        services: Services, ledger: Ledger, line: int, stage: str, handoff: bool,
    ) -> str | None:
        """One model call. Returns None when this line can no longer be paid for."""

        for delay in RETRY_BACKOFF_S + (None,):
            try:
                response = await services.llm.complete(
                    model=model,
                    messages=[
                        {"role": "system", "content": system},
                        {"role": "user", "content": user},
                    ],
                    max_tokens=max_tokens,
                    temperature=0.4,
                    # Measured: gpt-oss at high effort needs ~42k reasoning
                    # tokens on a hard problem before it emits any proof, above
                    # the 32k the harness allows, and it rejects
                    # reasoning.max_tokens with a 400.
                    reasoning={"effort": "medium"},
                )
            except BudgetExceeded as exc:
                # Reservation refused before the request went out, so the
                # ledger is intact and only this line stops.
                ledger.events.append({"line": line, "stage": stage, "model": model,
                                      "note": f"budget: {exc}"[:200]})
                return None
            except LLMCallError as exc:
                # Only a refusal releases its reservation. Every other failure
                # has already marked spend unknown, which zeroes the problem
                # however good the proof is, so a retry would buy nothing.
                if exc.status_code not in REFUSED_BEFORE_GENERATION:
                    raise
                if delay is None or self._time_left() <= delay or self._retries_left <= 0:
                    raise
                self._retries_left -= 1
                ledger.events.append({
                    "line": line, "stage": stage, "model": model,
                    "note": f"refused HTTP {exc.status_code}, retry in {delay:.0f}s,"
                            f" {self._retries_left} left",
                })
                await asyncio.sleep(delay)
                continue
            cost = ledger.record(response.usage)
            ledger.events.append({
                "line": line, "stage": stage, "model": model, "handoff": handoff,
                "cost_usd": round(cost, 6), "finish_reason": response.finish_reason,
            })
            return response.content
        return None


PLANNER_SYSTEM = """You are a competition mathematician preparing a proof for formalisation in Lean 4 with Mathlib.

Produce, in this order:
1. ANSWER: if the challenge file has any `abbrev NAME := sorry` slot, state the exact value each one must take. A numeric answer must be a plain decimal literal with no arithmetic.
2. PROOF: a complete, rigorous argument in English. Every step must be justified and no case may be skipped.
3. LEAN NOTES: the Mathlib lemma names and tactics the formalisation will need, and any step you expect to be hard in Lean.

Be concrete. The reader writes Lean directly from this and cannot consult you again."""

FORMALIZER_SYSTEM = """You write Lean 4 files that compile against a full Mathlib.

Rules:
- Return exactly one ```lean code block holding the complete file, starting with `import Mathlib`.
- Keep every theorem and definition name and statement from the challenge byte-identical. Only replace `sorry` bodies.
- Never emit sorry, admit, axiom, native_decide, or unsafe.
- An `abbrev NAME : ℕ := sorry` slot must become a plain decimal literal, for example `abbrev NAME : ℕ := 49`. No arithmetic expressions.
- Prefer short robust tactics: linarith, nlinarith, ring, field_simp, omega, decide, norm_num, simp, positivity, interval_cases.
- The file must compile as-is."""

REPAIRER_SYSTEM = """You repair Lean 4 files against Mathlib using compiler output.

Rules:
- Return exactly one ```lean code block holding the complete corrected file, starting with `import Mathlib`.
- Keep every theorem and definition name and statement byte-identical to the challenge.
- Never emit sorry, admit, axiom, native_decide, or unsafe.
- Read the error positions carefully. If a lemma name does not exist, replace it with one that does or prove the step by hand.
- If an approach has failed twice, change strategy rather than adjusting it."""


def planner_user(problem: Problem) -> str:
    return "\n".join([
        f"Problem id: {problem.id}", "",
        "Statement:", problem.description, "",
        "The Lean statement that must be proved:",
        "```lean", problem.challenge, "```",
    ])


def formalizer_user(problem: Problem, plan: str) -> str:
    parts = [
        f"Problem id: {problem.id}", "",
        "Statement:", problem.description, "",
        "Challenge file to complete:",
        "```lean", problem.challenge, "```",
    ]
    if plan.strip():
        parts += ["", "A mathematician's solution and formalisation notes:", plan.strip()]
    return "\n".join(parts)


def repairer_user(problem: Problem, line: Line, handoff: bool) -> str:
    parts = [f"Problem id: {problem.id}", ""]
    if handoff:
        parts += [
            "Another model has been working on this file and has stopped making progress.",
            "You are taking it over. Its notes and its current file follow. Feel free to",
            "discard its approach entirely if you see a better one.",
            "",
        ]
    parts += [
        "Statement:", problem.description, "",
        "Required names and statements, do not alter them:",
        "```lean", problem.challenge, "```",
    ]
    if line.plan.strip():
        parts += ["", "Solution notes for this attempt:", line.plan.strip()]
    parts += [
        "", "This file was submitted to Lean and rejected:",
        "```lean", line.candidate, "```",
        "", "Lean rejected it with:", "```text", line.feedback or "(no messages)", "```",
    ]
    return "\n".join(parts)


def create_agent() -> SubmissionAgent:
    return SubmissionAgent()
