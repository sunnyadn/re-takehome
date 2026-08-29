"""Two lines of attack, one per model, arbitrated by the Lean compiler.

A stalled line is handed to the other model. Rationale is in the writeup."""

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
from re_harness.lean import LeanRuntimeError, numeric_answers_are_literals
from re_harness.models import ALLOWED_MODELS, MODEL_A, MODEL_B

# A refused call releases its reservation, so repeating it is free and the
# problem stays winnable. Without this a single 429 ends the problem.
RETRY_BACKOFF_S = (5.0, 20.0, 60.0)
# A per-problem pool shared by both lines. Eight suited a 30-minute run of
# about 8 calls; a graded run makes roughly 35x that, so it scales.
RETRIES_PER_1800S = 8
PLAN_TOKENS = 16000
FORMALIZE_TOKENS = 16000
REPAIR_TOKENS = 16000
FEEDBACK_CHARS = 6000
# Each substitution costs one Lean check and no tokens.
MAX_SUBSTITUTIONS = 2
# Wins are early and cheap: the dearest of 54 recorded ones took 43 calls and
# $0.05, and none ever came later. Width buys more of that range than depth.
SLOT_TEMPERATURES = (0.2, 0.7, 1.0)
# Stop launching while a round still fits, since overshooting the ledger
# scores zero however good the proof is.
BUDGET_HEADROOM = 0.9


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
    # A cancelled call closes the ledger and scores the problem zero, so no
    # turn may start inside this window. A fixed margin was beaten by 2.4x.
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
    def max_retries(self) -> int:
        """Scales with the clock, which is what bounds retrying anyway."""

        return max(RETRIES_PER_1800S, round(RETRIES_PER_1800S * self.time_limit_s / 1800.0))

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
    temperature: float = 0.4
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

    The REPL checks against a full Mathlib; the Comparator compiles the file."""

    body = "\n".join(
        line for line in source.splitlines() if not line.lstrip().startswith("import ")
    ).strip()
    if not body:
        return fallback
    return "import Mathlib\n\n" + body + "\n"


FENCE_LINE = re.compile(r"^\s*```.*$", re.MULTILINE)


def strip_fences(block: str) -> str:
    """Remove fence lines a capture swallowed.

    One leftover backtick rejects the whole file."""

    return FENCE_LINE.sub("", block)


def extract_lean(text: str, fallback: str) -> str:
    fenced = re.findall(r"```(?:lean|lean4)?\s*\n(.*?)```", text, flags=re.DOTALL | re.IGNORECASE)
    for block in reversed(fenced):
        if strip_fences(block).strip():
            return normalise_imports(strip_fences(block), fallback)
    stripped = strip_fences(text).strip()
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

    Editing a header scores zero however well the proof compiles."""

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


def grade(source: str, check: Any, names: Sequence[str],
          challenge: str) -> tuple[list[str], int]:
    """What the grader would hold against this file, and how much."""

    faults = scoring_faults(source, names, challenge)
    faults += [f"{a} is not a permitted axiom, the grader rejects it"
               for a in forbidden_axioms(check.messages)]
    return faults, len(error_messages(check.messages)) + len(faults)


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

    Returns the source, bodies filled, and `sorry` placeholders left elsewhere."""

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

    One unknown name makes the whole `first` block fail to elaborate."""

    usable = []
    for tactic in COCKTAIL:
        probe = f"theorem vm_probe : True := by\n  first\n    | {wrap_tactic(tactic)}\n    | trivial"
        check = await services.lean.check_file(probe)
        if not any("unknown tactic" in str(m.get("data", "")) for m in check.messages):
            usable.append(tactic)
    return tuple(usable)


def sweep_files(source: str, cocktail: Sequence[str] = COCKTAIL) -> list[str]:
    """Deterministic candidates to try before spending a token on the models.

    Empty when a `sorry` survives outside the bodies: Lean can never accept it."""

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
    """Source lines holding a tactic that ran after its goal was closed.

    Lean strips imports first, so a position is offset by the imports above."""

    kept = [i for i, l in enumerate(source.splitlines(), start=1) if not IMPORT_LINE.match(l)]
    out = set()
    for m in messages:
        if m.get("severity") != "error" or NO_GOALS not in str(m.get("data", "")).lower():
            continue
        reported = (m.get("pos") or {}).get("line")
        if reported and 1 <= int(reported) <= len(kept):
            out.add(kept[int(reported) - 1])
    return sorted(out)


DECL_HEAD = re.compile(r"^(theorem|lemma|abbrev|def|example|noncomputable|private|@\[)")
MISSING_NAME = re.compile(r"unknown (constant|identifier)|environment does not contain", re.I)
TRY_THIS = "Try this"
# Every search that ever returned a hit finished within 18s; one that
# returned nothing ran 131s. Bounds the wasted wait, not the useful one.
LEMMA_SEARCH_TIMEOUT_S = 30
HINT_CHARS = 1500
# Counting searches measures the wrong thing: 30 of them is about 1% of the
# graded clock, yet 27 of 33 recorded runs would have wanted more than 30.
SEARCH_BUDGET_FRACTION = 0.05


def source_lines(
    messages: Sequence[dict[str, Any]], source: str, pattern: Any = None
) -> list[int]:
    """Source line of every positioned error, earliest first.

    With a pattern, only the errors whose text matches it."""

    kept = [i for i, l in enumerate(source.splitlines(), start=1) if not IMPORT_LINE.match(l)]
    out = []
    for m in messages:
        if m.get("severity") != "error":
            continue
        if pattern is not None and not pattern.search(str(m.get("data", ""))):
            continue
        reported = (m.get("pos") or {}).get("line")
        if reported and 1 <= int(reported) <= len(kept):
            out.append(kept[int(reported) - 1])
    return sorted(set(out))


def splice_at_failure(source: str, errline: int, tactic: str) -> str | None:
    """Replace the proof from `errline` on with `tactic`.

    The cut stays inside one declaration so the graded ones survive."""

    lines = source.splitlines()
    starts = [i + 1 for i, l in enumerate(lines) if DECL_HEAD.match(l)]
    if not starts or not 1 <= errline <= len(lines):
        return None
    begin = max((b for b in starts if b <= errline), default=None)
    if begin is None:
        return None
    end = min((b for b in starts if b > errline), default=len(lines) + 1) - 1
    proof = None
    for i in range(begin, end + 1):
        body = lines[i - 1].split("--")[0].rstrip()
        if body.endswith(" by") or body.endswith(":= by") or body.strip() == "by":
            proof = i + 1
            break
    if proof is None or proof > end:
        return None
    at = max(errline, proof)
    indent = lines[at - 1][: len(lines[at - 1]) - len(lines[at - 1].lstrip())] or "  "
    spliced = [f"{indent}{t}" for t in tactic.split("\n")]
    return "\n".join(lines[: at - 1] + spliced + lines[end:]) + "\n"


def search_file(source: str, errline: int) -> str | None:
    """The candidate with `apply?` where the proof first went wrong."""

    return splice_at_failure(source, errline, "all_goals apply?")


def resume_file(source: str, errline: int) -> str | None:
    """The proof kept only up to its first error, with the goal there printed.

    Lean states what is left to prove; regenerating the whole file discards it."""

    return splice_at_failure(source, errline, "trace_state\nsorry")


TRY_LINE = re.compile(r"^\s*\[[a-z]+\]\s*(\S.*?)\s*$")


def suggested_tactics(hits: Sequence[str]) -> list[str]:
    """The tactic Lean marked in each `Try this:` block.

    Blocks mix lemma terms with tactic advice; the marker picks out both."""

    out = []
    for hit in hits:
        for line in hit.splitlines():
            found = TRY_LINE.match(line)
            if found and found.group(1) not in out:
                out.append(found.group(1).strip())
    return out


def suggestions(messages: Sequence[dict[str, Any]]) -> list[str]:
    return [str(m.get("data", "")).strip() for m in messages
            if m.get("severity") == "info" and TRY_THIS in str(m.get("data", ""))]


def drop_lines(source: str, drop: Sequence[int]) -> str:
    removed = set(drop)
    kept = [l for i, l in enumerate(source.splitlines(), start=1) if i not in removed]
    return "\n".join(kept) + "\n"


HTTP_STATUS = re.compile(r"OpenRouter returned HTTP (\d{3})")


def refused_before_generation(exc: LLMCallError) -> bool:
    """Whether the provider refused this call before generating anything.

    The harness reports the status only in the message. A retry is safe."""

    found = HTTP_STATUS.search(str(exc))
    return bool(found) and int(found.group(1)) in REFUSED_BEFORE_GENERATION


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
        self._search_spent_s = 0.0
        self.config = config or Config.from_env()
        self._retries_left = self.config.max_retries

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        cfg = self.config
        started = time.monotonic()
        deadline = started + cfg.last_turn_start_s
        self._deadline = deadline
        self._retries_left = cfg.max_retries
        self._search_spent_s = 0.0
        ledger = Ledger()
        names = answer_names(problem.challenge)
        decls = declared_names(problem.challenge)
        lines = [Line(index=i, owner=m, temperature=t)
                 for i, (m, t) in enumerate(
                     (m, t) for t in SLOT_TEMPERATURES for m in cfg.lines)]
        best = normalise_imports(problem.challenge, problem.challenge)
        winner: int | None = None

        def time_left() -> float:
            return deadline - time.monotonic()

        def offer(line: Line, accepted: bool) -> bool:
            """Keep a candidate the grader could score; never rank the losers.

            Ranking by error count once submitted a file with the theorem deleted."""

            nonlocal best, winner
            if not line.candidate:
                return False
            if not accepted and scoring_faults(line.candidate, names, problem.challenge):
                return False
            best = line.candidate
            if accepted:
                winner = line.index
            services.checkpoint(best, {"line": line.index, "accepted": accepted})
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
                live = [l for l in lines if not l.done]
                if winner is not None or not live or time_left() <= 0:
                    break
                if ledger.spent_usd >= BUDGET_HEADROOM * cfg.budget_usd:
                    ledger.events.append({"stage": "stop", "note": "budget headroom"})
                    break
                # A barrier, never a race. Cancelling a call in flight marks
                # spend unknown, which zeroes a problem already proved.
                done = await asyncio.gather(
                    *(self._advance(problem, l, services, ledger, names, decls)
                      for l in live),
                    return_exceptions=True,
                )
                fatal = next((r for r in done if isinstance(r, BaseException)), None)
                for line, got in zip(live, done):
                    if got is True:
                        offer(line, True)
                if winner is None:
                    for line, got in zip(live, done):
                        if got is False:
                            offer(line, False)
                if fatal is not None:
                    raise fatal
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
                services, ledger, line.index, "plan", handoff, line.temperature,
            )
            if plan is None:
                line.done = True
                return False
            line.plan = plan
            content = await self._call(
                model, FORMALIZER_SYSTEM, formalizer_user(problem, line.plan), FORMALIZE_TOKENS,
                services, ledger, line.index, "formalize", handoff, line.temperature,
            )
        else:
            content = await self._call(
                model, REPAIRER_SYSTEM, repairer_user(problem, line, handoff), REPAIR_TOKENS,
                services, ledger, line.index, "repair", handoff, line.temperature,
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
        faults, line.errors = grade(line.candidate, check, names, problem.challenge)
        hint, tactics, at = await self._lemma_hint(
            line.candidate, check, ledger, line.index, services)
        swapped = await self._substitute(line, at, tactics, services, ledger, names,
                                         problem.challenge)
        if swapped is not None:
            line.candidate, check = swapped
            hint = []
            faults, line.errors = grade(line.candidate, check, names, problem.challenge)
            ledger.events.append({"line": line.index, "stage": "substituted", "at": at,
                                  "model": model, "errors": line.errors,
                                  "accepted": check.accepted})
        signature = "\n".join([error_signature(check.messages)] + faults)
        line.stalls = line.stalls + 1 if signature == line.signature else 0
        line.signature = signature
        line.feedback = "\n".join(faults + [format_messages(check.messages)] + hint).strip() or (
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

    async def _substitute(
        self, line: Line, at: int, tactics: Sequence[str], services: Services,
        ledger: Ledger, names: Sequence[str], challenge: str,
    ) -> tuple[str, Any] | None:
        """Splice a lemma Lean actually found, instead of asking for it.

        Requiring the whole file to compile never fired: 0 of 65 recorded
        searches ran on a file with one error, so take any strict drop."""

        best = None
        for tactic in tactics[:MAX_SUBSTITUTIONS]:
            if self._time_left() <= LEMMA_SEARCH_TIMEOUT_S:
                break
            fixed = splice_at_failure(line.candidate, at, tactic)
            if fixed is None:
                continue
            fixed = normalise_imports(fixed, line.candidate)
            if banned_constructs(fixed):
                continue
            try:
                check = await services.lean.check_file(fixed)
            except LeanRuntimeError:
                break
            faults, errors = grade(fixed, check, names, challenge)
            if faults or errors >= line.errors:
                continue
            if best is None or errors < best[1]:
                best = (fixed, errors, check)
            if check.accepted:
                break
        return (best[0], best[2]) if best else None

    async def _lemma_hint(
        self, source: str, check: Any, ledger: Ledger, index: int, services: Services,
    ) -> tuple[list[str], list[str], int]:
        """Ask Lean for a real lemma when the model invented one.

        Models state invented names confidently, so the real one is pushed."""

        budget = SEARCH_BUDGET_FRACTION * self.config.time_limit_s
        if self._search_spent_s >= budget or check.accepted:
            return [], [], 0
        # Search where the invented name is, not at the file's earliest error.
        # Those differ on 62% of triggering checks, and the hint tells the model
        # these lemmas are for the goal it got wrong.
        lines = source_lines(check.messages, source, MISSING_NAME)
        candidate = search_file(source, lines[0]) if lines else None
        if candidate is None or self._time_left() <= LEMMA_SEARCH_TIMEOUT_S:
            return [], [], 0
        started = time.monotonic()
        try:
            found = await services.lean.check_file(
                normalise_imports(candidate, source), timeout_s=LEMMA_SEARCH_TIMEOUT_S
            )
        except LeanRuntimeError:
            self._search_spent_s += time.monotonic() - started
            return [], [], 0
        self._search_spent_s += time.monotonic() - started
        hits = suggestions(found.messages)
        ledger.events.append({"line": index, "stage": "lemma_search",
                              "at": lines[0], "found": len(hits)})
        if not hits:
            return [], [], 0
        # A suggestion carries its remaining subgoals, so three of them can be
        # long. The message cap does not cover this block, so cap it here.
        block = "\n".join(hits[:3])[:HINT_CHARS]
        return (["Lean's own search found these real lemmas for the goal you got wrong. "
                 "The names you used may not exist; these do.", block],
                suggested_tactics(hits), lines[0])

    def _time_left(self) -> float:
        return float("inf") if self._deadline is None else self._deadline - time.monotonic()

    async def _call(
        self, model: str, system: str, user: str, max_tokens: int,
        services: Services, ledger: Ledger, line: int, stage: str, handoff: bool,
        temperature: float = 0.4,
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
                    temperature=temperature,
                    # Measured: at high effort gpt-oss wants ~42k reasoning
                    # tokens before emitting a proof, over the harness's 32k.
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
                if not refused_before_generation(exc):
                    raise
                if delay is None or self._time_left() <= delay or self._retries_left <= 0:
                    raise
                self._retries_left -= 1
                ledger.events.append({
                    "line": line, "stage": stage, "model": model,
                    "note": f"refused before generation, retry in {delay:.0f}s,"
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
