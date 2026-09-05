"""Two lines of attack, one per model, arbitrated by the Lean compiler.

A stalled line is handed to the other model. Rationale is in the writeup."""

from __future__ import annotations

import asyncio
import os
import copy
import dataclasses
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
from submission.techniques import PREAMBLE_MARK, preamble, technique_card

# A refused call releases its reservation, so repeating it is free and the
# problem stays winnable. Without this a single 429 ends the problem.
RETRY_BACKOFF_S = (5.0, 20.0, 60.0)
# A per-problem pool shared by both lines. Eight suited a 30-minute run of
# about 8 calls; a graded run makes roughly 35x that, so it scales.
RETRIES_PER_1800S = 8
PLAN_TOKENS = 16000
FEEDBACK_CHARS = 6000
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
    # Research switch: VM_AUDIT=off lets every statement in unaudited (the
    # ablation arm of the writeup). The judged configuration is the default.
    audit: bool = True
    # `VM_LEAVES=off` skips the shape-built tactic blocks (the ablation that
    # measures the hand-written layer's share). The judged configuration is on.
    leaves: bool = True
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
            audit=os.environ.get("VM_AUDIT", "on").strip().lower() not in ("off", "0", "false"),
            leaves=os.environ.get("VM_LEAVES", "on").strip().lower() not in ("off", "0", "false"),
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
class Ledger:
    """Local mirror of spend, which Services does not expose, plus a turn log."""

    spent_usd: float = 0.0
    events: list[dict[str, Any]] = field(default_factory=list)

    def record(self, usage: Any) -> float:
        # llm.complete validates usage.cost before returning, so this is total.
        cost = float(usage["cost"])
        self.spent_usd += cost
        return cost


NAT_POW_LINE = "attribute [instance 2000] instPowNat"
NUMERAL_EXPONENT = re.compile(r"\^ (\d+)(?![\d.])")
STATEMENT = re.compile(r"((?:theorem|lemma)\s+[\w'.]+)(.*?)(:=[ \t]*by\b)", re.S)


def type_exponents(text: str) -> str:
    """`x ^ 2` becomes `x ^ (2 : ℕ)` in every theorem statement. Under the
    challenge's own imports the numeral exponent elaborates through core's
    `instPowNat`; under `import Mathlib` a default instance routes it through
    `Monoid.npow`, and the comparator then sees two different statements."""

    return STATEMENT.sub(lambda m: m.group(1) + NUMERAL_EXPONENT.sub(r"^ (\1 : ℕ)", m.group(2))
                         + m.group(3), text)


def normalise_imports(source: str, fallback: str) -> str:
    """The challenge's own imports, kept, plus `import Mathlib` for the tactics.

    Measured on rmo_2000_6 (2026-09-03): a proof the REPL and `lake build`
    both accepted scored 0, "Challenge and solution theorem statement do not
    match", because `import Mathlib` alone made `a ^ 2` elaborate through
    `Monoid.npow` where the challenge's `import Mathlib.Data.Nat.Basic` used
    `instPowNat`. With the original imports kept, `instPowNat` raised above
    the default instance and numeral exponents typed, the comparator passes."""

    lines = source.splitlines()
    imports: list[str] = []
    for line in lines:
        if line.lstrip().startswith("import ") and line.strip() not in imports:
            imports.append(line.strip())
    body = "\n".join(line for line in lines if not line.lstrip().startswith("import ")).strip()
    if not body:
        return fallback
    if "import Mathlib" not in imports:
        imports.append("import Mathlib")
    if any(i != "import Mathlib" for i in imports):
        if NAT_POW_LINE not in body:
            body = NAT_POW_LINE + "\n\n" + body
        body = type_exponents(body)
    return "\n".join(imports) + "\n\n" + body + "\n"


def with_preamble(text: str) -> str:
    """The technique tactics (techniques.py), defined once after the header
    of a normalised file: imports, then the instance line if any."""
    if PREAMBLE_MARK in text:
        return text
    lines = text.split("\n")
    k = max((i for i, l in enumerate(lines) if l.startswith("import ") or l == NAT_POW_LINE), default=-1)
    return "\n".join(lines[:k + 1] + ["", preamble()] + lines[k + 1:])


FENCE_LINE = re.compile(r"^\s*```.*$", re.MULTILINE)


def strip_fences(block: str) -> str:
    """Remove fence lines a capture swallowed.

    One leftover backtick rejects the whole file."""

    return FENCE_LINE.sub("", block)


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

    # the header the agent writes is the challenge's after normalise_imports
    # (typed numeral exponents under narrow imports), so compare against that
    original = statement_headers(normalise_imports(challenge, challenge))
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
    "rfl", "trivial", "assumption", "norm_num", "simp", "omega", "positivity", "ring",
    "linarith", "nlinarith", "field_simp; ring", "simp; omega",
    "norm_num; omega", "constructor <;> norm_num", "simp_all", "aesop",
    "decide", "gcongr", "bound", "norm_cast", "push_cast; ring",
    "interval_cases <;> norm_num", "exact le_refl _", "tauto",
    "subst_vars <;> omega", "subst_vars <;> ring", "subst_vars <;> nlinarith", "constructor <;> omega",
    "refine ⟨?_, ?_⟩ <;> norm_num", "simp_all <;> omega", "zify; omega",
    "push_cast; omega", "ring_nf; omega", "ring_nf; nlinarith",
    "interval_cases <;> omega", "simp_arith", "constructor <;> simp",
    "refine ⟨?_, ?_, ?_⟩ <;> norm_num", "decide <;> norm_num",
    "field_simp; nlinarith", "rify; nlinarith", "omega <;> norm_num",
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


# One goal split into two is two easier goals, and `constructor` costs no
# tokens. Gated on the statement, so the other problems pay nothing.
SPLITTERS = ("intros", "constructor", "intros\n  constructor", "refine ⟨?_, ?_⟩")
SPLITTABLE = re.compile(r"↔|∧|∀")


def split_files(source: str, cocktail: Sequence[str] = COCKTAIL) -> list[str]:
    """Sweep candidates that decompose the goal before trying the library."""

    if not SPLITTABLE.search(source):
        return []
    alternation = "first\n" + "\n".join(f"      | {wrap_tactic(t)}" for t in cocktail)
    files = []
    for splitter in SPLITTERS:
        body, filled, left = splice_tactic(source, f"{splitter}\n  all_goals {alternation}")
        if filled and not left:
            files.append(normalise_imports(body, body))
    return files


IMPORT_LINE = re.compile(r"^\s*import\s")
NO_GOALS = "no goals to be solved"


def import_lines(source: str) -> int:
    return sum(1 for l in source.splitlines() if IMPORT_LINE.match(l))


class FileCoordinates:
    """The one place Lean's positions meet the file. The REPL client strips
    every import line before Lean sees the source, and Lean numbers the body
    it received from 1; each reported line moves down by the number of import
    lines so every reader works in file coordinates."""

    def __init__(self, inner: Any) -> None:
        self._inner = inner

    def __getattr__(self, name: str) -> Any:
        return getattr(self._inner, name)

    async def check_file(self, source: str, timeout_s: Any = None) -> Any:
        check = await self._inner.check_file(source, timeout_s=timeout_s)
        shift = import_lines(source)
        if not shift or not check.messages:
            return check
        moved = []
        for m in check.messages:
            m = dict(m)
            for key in ("pos", "endPos"):
                at = m.get(key)
                if isinstance(at, dict) and isinstance(at.get("line"), int):
                    m[key] = dict(at, line=at["line"] + shift)
            moved.append(m)
        if dataclasses.is_dataclass(check):
            return dataclasses.replace(check, messages=moved)
        check = copy.copy(check)
        check.messages = moved
        return check


def in_file_coordinates(services: Any) -> Any:
    if not isinstance(services.lean, FileCoordinates):
        services.lean = FileCoordinates(services.lean)
    return services


DECL_HEAD = re.compile(r"^(theorem|lemma|abbrev|def|example|noncomputable|private|@\[)")
TRY_THIS = "Try this"
# Counting searches measures the wrong thing: 30 of them is about 1% of the
# graded clock, yet 27 of 33 recorded runs would have wanted more than 30.
SEARCH_BUDGET_FRACTION = 0.05


UNSOLVED = "unsolved goals"


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


def format_messages(messages: Sequence[dict[str, Any]]) -> str:
    """Keep the earliest diagnostics, since later ones usually cascade."""

    chunks = [
        f"{m.get('severity')} at {m.get('pos')}: {str(m.get('data', '')).strip()}"
        for m in messages
        if m.get("severity") in ("error", "warning")
    ]
    return "\n\n".join(chunks)[:FEEDBACK_CHARS] if chunks else ""


PLANNER_SYSTEM = """You are a competition mathematician preparing a proof for formalisation in Lean 4 with Mathlib.

Produce, in this order:
1. ANSWER: if the challenge file has any `abbrev NAME := sorry` slot, state the exact value each one must take. A numeric answer must be a plain decimal literal with no arithmetic.
2. PROOF: a complete, rigorous argument in English. Every step must be justified and no case may be skipped.
3. LEAN NOTES: the Mathlib lemma names and tactics the formalisation will need, and any step you expect to be hard in Lean.

Choose a plan Lean can check cheaply:
- Reduce the infinite to the finite. Bound the unknown between two explicit values, or use periodicity modulo a small number, or induct. State the bound.
- Leave the finite part to interval_cases, decide, or omega. Do not hand-prove what enumeration closes.
- Stay in the type the statement uses. Changing the ambient type costs one cast lemma at every later step, so take that route only if no omega or nlinarith route exists.

Be concrete. The reader writes Lean directly from this and cannot consult you again."""


def create_agent():
    """The graded entry point: the goal board.

    Imported here, not at module scope, because that module imports this one."""

    from submission.board_agent import create_agent as board_agent
    return board_agent()

