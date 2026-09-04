"""Conjecture a two-parameter generalisation of a sum identity that direct
induction cannot prove: split the variable's occurrences into two groups,
tabulate the family in Lean, fit a library of shapes, keep exact matches."""
from __future__ import annotations

import json
import re
from itertools import product
from math import comb as _comb
from typing import Any, Sequence

RANGE_BOUND = re.compile(r"Finset\.(?:range \((\w+) \+ 1\)|Icc 0 (\w+))")
EVAL_TAG = "vm_table"
GRID = (6, 7)          # n rows, k columns tabulated
VERIFY = 11            # n, k < VERIFY checked before a fit is posted


def comb(n: int, k: int) -> int:
    return _comb(n, k) if n >= 0 and 0 <= k <= n else 0


def occurrences(lhs: str, k: str) -> list[tuple[int, int]]:
    """Spans of the variable in the left-hand side, the range bounds excluded."""
    bounds = {m.start(1 if m.group(1) else 2) for m in RANGE_BOUND.finditer(lhs)}
    return [(m.start(), m.end()) for m in re.finditer(rf"(?<![\w'.]){re.escape(k)}(?![\w'])", lhs)
            if m.start() not in bounds]


def families(lhs: str, k: str, fresh: str) -> list[str]:
    """Every family F(fresh, k) got by renaming a nonempty proper-or-full subset
    of the non-bound occurrences of k to `fresh`; the bound stays k."""
    spots = occurrences(lhs, k)
    out: list[str] = []
    for r in range(1, len(spots) + 1):
        for chosen in _subsets(spots, r):
            text = lhs
            for a, b in sorted(chosen, reverse=True):
                text = text[:a] + fresh + text[b:]
            if text not in out:
                out.append(text)
    return out


def _subsets(items: Sequence[Any], r: int) -> list[tuple[Any, ...]]:
    if r == 0:
        return [()]
    if not items:
        return []
    first, rest = items[0], items[1:]
    return [(first,) + s for s in _subsets(rest, r - 1)] + _subsets(rest, r)


def table_file(prefix: str, family: str, fresh: str, k: str, index: int) -> str:
    """A Lean file that prints the family's values on the grid."""
    rows, cols = GRID
    return (f"{prefix}\ndef {EVAL_TAG}_{index} ({fresh} {k} : ℕ) : ℕ := {family}\n"
            f"#eval (List.range {rows}).map fun {fresh} => (List.range {cols}).map fun {k} => "
            f"{EVAL_TAG}_{index} {fresh} {k}\n")


def read_table(messages: Sequence[dict[str, Any]]) -> list[list[int]] | None:
    for m in messages:
        if m.get("severity") not in ("info", "information"):
            continue
        text = str(m.get("data", "")).strip()
        if text.startswith("[["):
            try:
                got = json.loads(text)
            except ValueError:
                continue
            if all(isinstance(r, list) and all(isinstance(x, int) for x in r) for r in got):
                return got
    return None


def shapes(n: str, k: str) -> list[tuple[str, Any]]:
    """(Lean expression in n and k, evaluator) for the closed and sum forms tried."""
    out: list[tuple[str, Any]] = []
    for c in range(0, 3):
        plus = f" + {c}" if c else ""
        out.append((f"Nat.choose ({n} + {k}{plus}) {k}", lambda a, b, c=c: comb(a + b + c, b)))
        out.append((f"Nat.choose ({n} + {k}{plus}) {n}", lambda a, b, c=c: comb(a + b + c, a)))
        out.append((f"∑ i ∈ Finset.range ({k} + 1), Nat.choose ({n} + {k}{plus}) i",
                    lambda a, b, c=c: sum(comb(a + b + c, i) for i in range(b + 1))))
        out.append((f"∑ i ∈ Finset.range ({n} + 1), Nat.choose ({n} + {k}{plus}) i",
                    lambda a, b, c=c: sum(comb(a + b + c, i) for i in range(a + 1))))
        out.append((f"2 ^ ({n} + {k}{plus}) - ∑ i ∈ Finset.range ({n} + 1), Nat.choose ({n} + {k}{plus}) i",
                    lambda a, b, c=c: 2 ** (a + b + c) - sum(comb(a + b + c, i) for i in range(a + 1))))
        for base in (2, 3):
            out.append((f"∑ i ∈ Finset.range ({k} + 1), {base} ^ i * Nat.choose ({n} + {k}{plus}) i",
                        lambda a, b, c=c, base=base: sum(base ** i * comb(a + b + c, i) for i in range(b + 1))))
            for d in range(0, 2):
                dp = f" + {d}" if d else ""
                out.append((f"{base} ^ ({k}{dp}) * Nat.choose ({n} + {k}{plus}) {k}",
                            lambda a, b, c=c, d=d, base=base: base ** (b + d) * comb(a + b + c, b)))
    for base in (2, 3, 4):
        for c in range(0, 3):
            plus = f" + {c}" if c else ""
            out.append((f"{base} ^ ({n} + {k}{plus})", lambda a, b, c=c, base=base: base ** (a + b + c)))
            out.append((f"{base} ^ ({k}{plus})", lambda a, b, c=c, base=base: base ** (b + c)))
    return out


def fits(table: Sequence[Sequence[int]], n: str, k: str, family: str) -> list[str]:
    """Shapes agreeing with every table entry, the family's own text excluded."""
    found = []
    for text, g in shapes(n, k):
        if text == family:
            continue
        try:
            ok = all(g(a, b) == table[a][b] for a in range(len(table)) for b in range(len(table[0])))
        except (ValueError, OverflowError, ZeroDivisionError):
            ok = False
        if ok:
            found.append(text)
    return found


def verify_file(prefix: str, family: str, guess: str, fresh: str, k: str) -> str:
    """A Lean file printing `true` when family and guess agree below VERIFY."""
    return (f"{prefix}\n#eval (List.range {VERIFY}).all fun {fresh} => (List.range {VERIFY}).all fun {k} => "
            f"decide (({family}) = ({guess}))\n")


def verified(messages: Sequence[dict[str, Any]]) -> bool:
    return any(m.get("severity") in ("info", "information") and str(m.get("data", "")).strip() == "true"
               for m in messages)


def lemma_text(name: str, fresh: str, k: str, family: str, guess: str) -> str:
    return f"theorem {name} ({fresh} {k} : ℕ) :\n    {family} = {guess} := by\n  sorry\n"
