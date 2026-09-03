"""Leaf candidates: tactic blocks generated from the shape of a goal, tried by
Lean with no model asked. Measured on 3 September: the models found the routes
on rmo_2000_2, rmo_2001_2 and putnam_2018_a1 within minutes and lost the runs
on leaves of these shapes (ℕ subtraction under a bound, a perfect power between
consecutive powers, a bounded variable, the divisors of a product)."""
from __future__ import annotations

import re

NUM = re.compile(r"^\d+$")
VAR = re.compile(r"^[A-Za-z_][\w']*$")
FINISH = "first | omega | (norm_num at *; done) | nlinarith | simp_all"
LEAF_CAP = 6
CASES_MAX = 40
# One check's elaboration is bounded: a candidate that does not finish fast is not one.
BUDGET = "set_option maxHeartbeats 60000 in"


def _hyps(goal_text: str) -> list[tuple[str, str]]:
    head = goal_text.split("⊢", 1)[0] if "⊢" in goal_text else ""
    out = []
    for line in head.split("\n"):
        if line[:1].isspace() or line.startswith("case ") or " : " not in line:
            continue
        names, typ = line.split(" : ", 1)
        for n in names.split():
            out.append((n, typ.strip()))
    return out


def _target(goal_text: str) -> str:
    return goal_text.rsplit("⊢", 1)[-1].strip() if "⊢" in goal_text else ""


def _bounds(hyps) -> list[tuple[str, str, str, int]]:
    """(name, variable, kind, numeral): kind "lower" for `c ≤ v` / `v ≥ c`
    (numeral c), "upper" for `v ≤ c` / `v < c` (numeral the largest value)."""
    out = []
    for n, t in hyps:
        m = re.match(r"^(\S+) (≤|<|≥|>) (\S+)$", t)
        if not m:
            continue
        a, op, b = m.groups()
        if op in ("≤", "<") and NUM.match(a) and VAR.match(b):
            out.append((n, b, "lower", int(a) + (1 if op == "<" else 0)))
        elif op in ("≥", ">") and VAR.match(a) and NUM.match(b):
            out.append((n, a, "lower", int(b) + (1 if op == ">" else 0)))
        elif op in ("≤", "<") and VAR.match(a) and NUM.match(b):
            out.append((n, a, "upper", int(b) - (1 if op == "<" else 0)))
    return out


def _powers(hyps) -> list[tuple[str, str, str, str]]:
    """(name, variable, exponent, rhs) for `v ^ n = rhs`."""
    out = []
    for n, t in hyps:
        m = re.match(r"^([A-Za-z_][\w']*) \^ ([23]) = (.+)$", t)
        if m:
            out.append((n, m.group(1), m.group(2), m.group(3).strip()))
    return out


def leaf_candidates(goal_text: str) -> list[str]:
    hyps = _hyps(goal_text)
    target = _target(goal_text)
    bounds = _bounds(hyps)
    powers = _powers(hyps)
    # The tightest bounds first; `0 < v` carries nothing a subtraction needs.
    lowers = sorted(((n, v, c) for n, v, kind, c in bounds if kind == "lower" and c >= 2),
                    key=lambda b: -b[2])
    out: list[str] = []

    # y = E with y ^ n known: squeeze between consecutive powers.
    m = re.match(r"^([A-Za-z_][\w']*) = (.+)$", target)
    if m and not NUM.match(m.group(2).strip()):
        y, rhs = m.group(1), m.group(2).strip()
        for _, v, n, _ in powers:
            if v == y:
                for hn, _, _ in lowers[:2]:
                    out.append(f"pow_squeeze {y} {n} ({rhs}) with {hn}")
                out.append(f"pow_squeeze {y} {n} ({rhs})")
    # d ∣ N: one goal per divisor, each finished mechanically.
    for n, t in hyps:
        if re.match(r"^.+ ∣ .+$", t) and re.search(r"\d", t):
            out.append(f"divisor_cases {n} <;> {FINISH}")
    # A bound below on a variable and ℕ subtraction or a polynomial: substitute.
    if lowers and ("-" in goal_text or "^" in goal_text):
        for hn, _, _ in lowers[:2]:
            out.append(f"obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le {hn}\nsubst hk\n"
                       "first | omega | nlinarith | (ring_nf at *; omega) | (ring_nf at *; nlinarith)")
    # A variable bounded above by a small numeral: every value.
    for _, v, kind, c in bounds:
        if kind == "upper" and c <= CASES_MAX:
            out.append(f"interval_cases {v} <;> {FINISH}")
    # v ^ n = numeral: v is bounded by the root.
    for _, v, n, rhs in powers:
        if NUM.match(rhs):
            root = int(round(int(rhs) ** (1 / int(n)))) + 1
            if root <= CASES_MAX:
                out.append(f"bounded_cases {v} {root}")
    seen, uniq = set(), []
    for c in out:
        if c not in seen:
            seen.add(c)
            uniq.append(c)
    return [f"{BUDGET}\n{c}" if not c.startswith("obtain") else c for c in uniq[:LEAF_CAP]]
