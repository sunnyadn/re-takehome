"""Audit by sampling: a statement over a sequence `x : ℕ → ℝ` (with ∀-hypotheses
over ℕ) is evaluated in Lean over ℚ at concrete sequences and small values, the
∀s bounded; a sample that meets every hypothesis and breaks the claim refutes it."""
from __future__ import annotations

import re
from typing import Any, Sequence

FORALL_BOUND = 12       # ∀ (N : ℕ), P  is checked as  ∀ N < 12, P
VALUE_BOUND = 8         # every ℕ binder ranges over 0..7
SEQ_TYPES = ("ℕ → ℝ", "ℕ → ℚ")
# Positive, non-increasing sequences of several decay rates; the first few
# also satisfy a summability bound like ∑ x(i²)/i ≤ 1 (measured on rmo_2000_3).
SAMPLES: tuple[str, ...] = (
    "fun n => 1 / ((n : ℚ) + 1)",
    "fun n => 1 / ((n : ℚ) + 1) ^ 2",
    "fun n => 1 / (2 * (n : ℚ) + 2)",
    "fun n => if n < 2 then 1 / 2 else 1 / (2 * (n : ℚ))",
    "fun n => 1 / 4",
    "fun n => 2 / ((n : ℚ) + 2)",
)
FORALL = re.compile(r"∀ \((\w+) : ℕ\),")


def sampled_search(groups: Sequence[str], target: str) -> tuple[list[str], str, str] | None:
    """(ℕ names, the sequence's name, the decidable body over ℚ) or None when a
    binder is neither ℕ, a sequence, nor a proposition the surgery can bound."""

    names, seq, hyps = [], None, []
    for g in groups:
        inner = g.strip()[1:-1]
        parts = inner.split(" : ", 1)
        if len(parts) != 2:
            return None
        typ = parts[1].strip()
        if typ == "ℕ":
            names += parts[0].split()
        elif typ in SEQ_TYPES and seq is None and len(parts[0].split()) == 1:
            seq = parts[0].strip()
        elif re.search(r"[=<≤>≥≠]", typ) and "∃" not in typ and "→" not in typ.replace("ℕ → ℝ", ""):
            hyps.append(bound_foralls(typ))
        else:
            return None
    if seq is None or "∃" in target or re.search(r"\bfun\b|λ", target):
        return None
    body = " && ".join(hyps + [f"!({bound_foralls(target.strip())})"])
    return names, seq, rationalise(body)


def hypotheses_only(body: str) -> str:
    """The body without its last conjunct (the negated claim)."""
    return body.rsplit(" && !(", 1)[0] if " && !(" in body else "true"


def bound_foralls(prop: str) -> str:
    """The proposition as a Bool: every `∀ (N : ℕ), P` is `P` decided over
    N < FORALL_BOUND (the instance search for the bounded ∀ is what fails)."""
    found = FORALL.match(prop.strip())
    if found:
        return (f"((List.range {FORALL_BOUND}).all fun {found.group(1)} => "
                f"{bound_foralls(prop.strip()[found.end():].strip())})")
    return f"decide ({prop.strip()})"


def rationalise(text: str) -> str:
    return text.replace("ℝ", "ℚ")


def sample_file(prefix: str, names: Sequence[str], seq: str, body: str) -> str:
    """A Lean `#eval` over the sample sequences and the ℕ binders below
    VALUE_BOUND, printing the first refutation as [sample index, values...]."""

    loops = "".join(f"{'  ' * (i + 2)}for {n} in List.range {VALUE_BOUND} do\n"
                    for i, n in enumerate(names))
    pad = "  " * (len(names) + 2)
    samples = ",\n    ".join(f"({s} : ℕ → ℚ)" for s in SAMPLES)
    tuple_ = ", ".join(["si"] + list(names))
    # Whether any sample meets every hypothesis at all: without one, "no
    # refutation" says nothing and the auditor is asked instead.
    met = hypotheses_only(body)
    for n in reversed(names):
        met = f"((List.range {VALUE_BOUND}).any fun {n} => {met})"
    return (prefix.rstrip("\n") + "\n\n"
            f"def vm_samples : List (ℕ → ℚ) := [\n    {samples}]\n\n"
            "#eval Id.run do\n  let mut found : List (List Nat) := []\n"
            "  for si in List.range vm_samples.length do\n"
            f"    let {seq} := vm_samples.getD si (fun _ => 0)\n"
            + loops + f"{pad}if found.length < 1 && ({body}) then\n"
            + f"{pad}  found := found ++ [[{tuple_}]]\n  return found\n\n"
            "#eval vm_samples.any fun " + seq + " => " + met + "\n")


def read_sample_hit(messages: Sequence[dict[str, Any]],
                    names: Sequence[str]) -> tuple[bool, dict[str, str] | None]:
    """(some sample met every hypothesis, the refuting sample and values or None)."""
    import json
    met, hit = False, None
    for m in messages:
        if m.get("severity") not in ("info", "information"):
            continue
        text = str(m.get("data", "")).strip()
        if text == "true":
            met = True
        if not text.startswith("[["):
            continue
        try:
            rows = json.loads(text)
        except ValueError:
            continue
        if rows and len(rows[0]) == len(names) + 1:
            row = rows[0]
            hit = {"sequence": SAMPLES[row[0]] if 0 <= row[0] < len(SAMPLES) else str(row[0])}
            hit.update({n: str(v) for n, v in zip(names, row[1:])})
    return met or hit is not None, hit
