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


def _powered(hyps) -> list[tuple[str, str, str, str]]:
    """(name, variable, exponent, rest) for every hypothesis with `v ^ n` on one
    side of =, ≤ or <, n = 2 or 3."""
    out = []
    for n, t in hyps:
        m = re.match(r"^(.+?) (=|≤|<|≥|>) (.+)$", t)
        if not m:
            continue
        for side in (m.group(1), m.group(3)):
            p = re.match(r"^([A-Za-z_][\w']*) \^ ([23])$", side.strip())
            if p:
                out.append((n, p.group(1), p.group(2), t))
    return out


def _shifts(rhs: str, n: int) -> list[str]:
    """For P = v ^ n + a * v ^ (n-1) + ..., the E with E ^ n ≤ P < (E + 1) ^ n
    for large v: v + a // n, and v + a // n - 1 when a divides evenly."""
    m = re.match(rf"^([A-Za-z_][\w']*) \^ {n} \+ (\d+) \* \1 \^ {n - 1}\b", rhs)
    if not m:
        m2 = re.match(rf"^([A-Za-z_][\w']*) \^ {n} \+ \1 \^ {n - 1}\b", rhs)
        if not m2:
            return []
        v, a = m2.group(1), 1
    else:
        v, a = m.group(1), int(m.group(2))
    k = a // n
    out = [f"{v} + {k}" if k else v]
    if a % n == 0 and k >= 1:
        out.append(f"{v} + {k - 1}" if k > 1 else v)
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

    # v ^ n bounded by powers in the context (on v ^ n itself, or through
    # `v ^ n = P`), the goal about v: the bounds move to v, then omega. Measured
    # on rmo_2000_2 (v7.79): the route left `h_low : (x+2)^3 ≤ P`, `h_up : P ≤
    # (x+3)^3`, `h : y^3 = P ⊢ y = x + 2 ∨ y = x + 3`, and no model closed it.
    for _, v, n, _ in _powered(hyps):
        if re.search(rf"\b{re.escape(v)}\b", target) and any(
                re.search(r"(≤|<)", t) and re.search(r"\^ " + n + r"\b", t) for _, t in hyps):
            out.append(f"pow_bounds {v} {n}")

    # y = E with y ^ n known: squeeze between consecutive powers.
    m = re.match(r"^([A-Za-z_][\w']*) = (.+)$", target)
    if m and not NUM.match(m.group(2).strip()) and not re.search(r"[∨∧↔→]", m.group(2)):
        y, rhs = m.group(1), m.group(2).strip()
        for _, v, n, _ in powers:
            if v == y:
                for hn, _, _ in lowers[:2]:
                    out.append(f"pow_squeeze {y} {n} ({rhs}) with {hn}")
                out.append(f"pow_squeeze {y} {n} ({rhs})")
    # `v ≤ c` / `v < c` / False with y ^ n = P(v): for v large, P sits strictly
    # between consecutive n-th powers of v + k, k read off P's leading terms.
    # Measured on rmo_2000_2 (v7.79): the board was one goal short, `x ≤ 9`,
    # for 40 minutes; by contradiction the strict squeeze closes it.
    up = re.match(r"^([A-Za-z_][\w']*) (≤|<) (\d+)$", target)
    for _, y, n, rhs in powers:
        for e in _shifts(rhs, int(n)):
            if up and up.group(1) in rhs and up.group(1) != y:
                out.append(f"by_contra hc\npush_neg at hc\npow_squeeze {y} {n} ({e}) with hc")
            elif target == "False":
                for hn, _, _ in lowers[:2]:
                    out.append(f"pow_squeeze {y} {n} ({e}) with {hn}")
                out.append(f"pow_squeeze {y} {n} ({e})")
    # A variable defined by an equation `w = E`: substitute, make ℕ subtraction
    # exact, then arithmetic. Measured on rmo_2000_2: `hyx : y = x + 2 ⊢ x = 9`.
    for hn, t in hyps:
        d = re.match(r"^([A-Za-z_][\w']*) = (.+)$", t)
        if d and not NUM.match(d.group(2).strip()) and re.search(r"[A-Za-z]", d.group(2)) \
                and not re.search(r"[∨∧↔→∀∃∣]", goal_text):
            out.append(f"subst {hn}\n{'nat_sub_exact' + chr(10) if '-' in goal_text else ''}"
                       "first | omega | nlinarith | (ring_nf at *; omega) | (ring_nf at *; nlinarith)")
            break
    if "-" in goal_text and not re.search(r"[∨∧↔→∀∃∣]", target):
        out.append("nat_sub_exact\nfirst | omega | nlinarith | (ring_nf at *; omega) | (ring_nf at *; nlinarith)")
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
    return [f"{BUDGET}\n{c}" if not c.startswith(("obtain", "subst", "by_contra")) else c
            for c in uniq[:LEAF_CAP]]
