"""The first attempt, which costs nothing.

One block of alternative tactics spliced into every placeholder, under three
`set_option` preambles, and again behind four ways of splitting a goal. Ten of
the sixteen sample problems close here with no model asked."""

from __future__ import annotations

import re
from typing import Sequence

from re_harness import Services
from submission.contract import normalise_imports


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

