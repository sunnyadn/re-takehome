"""Leaf candidates: tactic blocks generated from the shape of a goal, tried by
Lean with no model asked. Measured on 3 September: the models found the routes
on rmo_2000_2, rmo_2001_2 and putnam_2018_a1 within minutes and lost the runs
on leaves of these shapes (ℕ subtraction under a bound, a perfect power between
consecutive powers, a bounded variable, the divisors of a product)."""
from __future__ import annotations

import re

NUM = re.compile(r"^\d+$")
VAR = re.compile(r"^[A-Za-z_][\w']*$")
# Every alternative must close the goal: `simp_all` alone can rewrite a
# hypothesis, count as success, and leave the goal open (measured on the
# rmo_2001_2 case leaves).
FINISH = ("first | omega | (norm_num at *; done) | nlinarith | (simp_all; done)"
          " | (simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, "
          "Finset.mem_insert, Finset.mem_singleton] at *; omega)")
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


class _Nat(int):
    """ℕ arithmetic for evaluating a printed polynomial: subtraction truncates."""
    def __add__(self, o): return _Nat(int(self) + int(o))
    def __radd__(self, o): return _Nat(int(o) + int(self))
    def __sub__(self, o): return _Nat(max(0, int(self) - int(o)))
    def __rsub__(self, o): return _Nat(max(0, int(o) - int(self)))
    def __mul__(self, o): return _Nat(int(self) * int(o))
    def __rmul__(self, o): return _Nat(int(o) * int(self))
    def __pow__(self, o): return _Nat(int(self) ** int(o))


def _evaluate(expr: str, var: str, value: int):
    """The printed ℕ expression at var = value, or None if it is not one."""
    if not re.fullmatch(r"[\w\s+\-*^()']+", expr) or re.search(r"[A-Za-z_][\w']*", expr.replace(var, "")):
        return None
    try:
        return int(eval(re.sub(rf"\b{re.escape(var)}\b", f"_Nat({value})", expr).replace("^", "**"),
                        {"__builtins__": {}}, {"_Nat": _Nat}))
    except Exception:  # noqa: BLE001 - a shape the evaluator does not read is not a leaf
        return None


def _threshold(p: str, e: str, n: int, var: str) -> int | None:
    """The T with sign(P(x) - E(x)^n) fixed for x ≥ T, from a scan to CASES_MAX;
    None when the sign never settles or never changes."""
    signs = []
    for x in range(CASES_MAX + 1):
        pv, ev = _evaluate(p, var, x), _evaluate(e, var, x)
        if pv is None or ev is None:
            return None
        d = pv - ev ** n
        signs.append((d > 0) - (d < 0))
    last = signs[-1]
    t = max((i + 1 for i, sg in enumerate(signs) if sg != last), default=0)
    return t if 1 <= t <= CASES_MAX else None


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


def _primes(hyps) -> list[str]:
    return [n for n, t in hyps if re.match(r"^Nat\.Prime [A-Za-z_][\w']*$", t)]


def _prime_facts(hyps) -> str:
    """`2 ≤ p` for every `hp : Nat.Prime p`: what omega and nlinarith need and
    a printed context never carries."""
    return "".join(f"have hge_{n} := Nat.Prime.two_le {n}\n" for n in _primes(hyps))


def _solved_subtractions(hyps) -> list[tuple[str, str, str]]:
    """(name, `v = t₁ + t₂ + (D)`, D) for a hypothesis `v - t₁ - t₂ = D`: omega
    solves it once D is known positive and the rest of the context is out of
    the way (measured: a nonlinear hypothesis sharing the subtraction made
    omega give up on a linear fact it proves alone)."""
    out = []
    for n, t in hyps:
        m = re.match(r"^([A-Za-z_][\w']*)((?: - [^-=()]+)+) = (.+)$", t)
        if m and not re.search(r"[∨∧↔→]", t):
            terms = [x.strip() for x in m.group(2).split(" - ") if x.strip()]
            d = m.group(3).strip()
            out.append((n, f"{m.group(1)} = {' + '.join(terms)} + ({d})", d))
    return out


def _finish(target: str) -> str:
    """The closing chain; a disjunction also tries each disjunct."""
    if "∨" not in target:
        return FINISH
    return (FINISH + " | (left; nlinarith) | (right; left; constructor <;> nlinarith)"
            " | (right; right; constructor <;> nlinarith) | (right; nlinarith)")


def _claims_about(target: str, y: str, n: str) -> list[tuple[str, str]]:
    """(E, x) for a target comparing y with E or y ^ n with E ^ n, x the one
    variable of E other than y."""
    out = []
    for m in (re.match(rf"^{re.escape(y)} (?:≤|<|≥|>|=) (.+)$", target),
              re.match(rf"^(.+) (?:≤|<|≥|>|=) {re.escape(y)}$", target),
              re.match(rf"^{re.escape(y)} \^ {n} (?:≤|<|≥|>) \((.+)\) \^ {n}$", target),
              re.match(rf"^\((.+)\) \^ {n} (?:≤|<|≥|>) {re.escape(y)} \^ {n}$", target)):
        if m:
            e = m.group(1).strip()
            names = sorted(set(re.findall(r"[A-Za-z_][\w']*", e)) - {y})
            if len(names) == 1 and not re.search(r"[∨∧↔→]", e):
                out.append((e, names[0]))
    return out


def leaf_candidates(goal_text: str) -> list[str]:
    hyps = _hyps(goal_text)
    target = _target(goal_text)
    bounds = _bounds(hyps)
    powers = _powers(hyps)
    primes = _prime_facts(hyps)
    finish = _finish(target)
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
    # A claim about y against E (y ≤ E, E ≤ y, E ^ n ≤ y ^ n, ...) under
    # y ^ n = P(x) that holds only from some x on: below the threshold the
    # equation has no solution (every x, then every y, by cases), above it the
    # arithmetic goes through. Measured on rmo_2000_2 (v7.84, second run):
    # `⊢ (x + 2) ^ 3 ≤ y ^ 3` and `⊢ y ≤ x + 2` were posted with no case split
    # and 26 leaf tries went nowhere.
    for _, y, n, rhs in powers:
        for e, x in _claims_about(target, y, n):
            t = _threshold(rhs, e, int(n), x)
            if t is None:
                continue
            small = max((_evaluate(rhs, x, v) or 0) for v in range(t))
            root = int(round(small ** (1 / int(n)))) + 2
            if root > CASES_MAX:
                continue
            out.append(f"rcases Nat.lt_or_ge {x} {t} with hlt | hge\n"
                       f"· interval_cases {x} <;> first | omega | (bounded_cases {y} {root})\n"
                       f"· obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hge\n  subst hk\n"
                       f"  first | omega | nlinarith | (ring_nf at *; omega) | (ring_nf at *; nlinarith)")
            break
    # A variable defined by an equation `w = E`: substitute, make ℕ subtraction
    # exact, then arithmetic. Measured on rmo_2000_2: `hyx : y = x + 2 ⊢ x = 9`.
    for hn, t in hyps:
        d = re.match(r"^([A-Za-z_][\w']*) = (.+)$", t)
        if d and not NUM.match(d.group(2).strip()) and re.search(r"[A-Za-z]", d.group(2)) \
                and not re.search(r"[↔→∀∃∣]", goal_text):
            out.append(f"{primes}subst {hn}\n{'nat_sub_exact' + chr(10) if '-' in goal_text else ''}"
                       + finish)
            break
    # A variable defined through ℕ subtraction, `m - p - q = D`: solve for it and
    # substitute. Measured on rmo_2001_2 (v7.79): divisor_cases left eight such
    # cases and every model reply on them failed at the truncated subtraction.
    for hn, eq, d in _solved_subtractions(hyps):
        if not re.search(r"[↔→∀∃]", target):
            keep = " ".join([hn, "hpos_d"] + [f"hge_{n}" for n in _primes(hyps)])
            out.append(f"{primes}have hpos_d : 0 < ({d}) := by first | omega | positivity | nlinarith\n"
                       f"have hsolve : {eq} := by first | omega | (clear * - {keep}; omega)\n"
                       f"subst hsolve\n{finish}")
            break
    # A disjunction of such equations (what divisor_cases leaves as a fact):
    # every case at once, the same block in each. Measured on rmo_2001_2
    # (v7.87): the eight-way fact was on the board four times and the models
    # never split it inside the clock.
    for hn, t in hyps:
        cases = [c.strip() for c in t.split(" ∨ ")]
        if len(cases) < 2 or not re.search(r"[∨]", t) or re.search(r"[↔→∀∃]", target):
            continue
        heads = [re.match(r"^([A-Za-z_][\w']*)((?: - [^-=()]+)+) = (.+)$", c) for c in cases]
        if not all(heads) or len({(h.group(1), h.group(2)) for h in heads}) != 1:
            continue
        v, sub = heads[0].group(1), heads[0].group(2)
        terms = [x.strip() for x in sub.split(" - ") if x.strip()]
        lhs = f"{v}{sub}"
        keep = " ".join(["hc", "hpos_d"] + [f"hge_{n}" for n in _primes(hyps)])
        alts = " | ".join(["hc"] * len(cases))
        out.append(f"rcases {hn} with {alts} <;> ({primes.replace(chr(10), '; ')}"
                   f"have hpos_d : 0 < {lhs} := by first | omega | positivity | nlinarith; "
                   f"have hsolve : {v} = {' + '.join(terms)} + ({lhs}) := by first | omega | (clear * - {keep}; omega); "
                   f"rw [hc] at hsolve; subst hsolve; {finish})")
        break
    if "-" in goal_text and not re.search(r"[↔→∀∃∣]", target):
        out.append(f"{primes}nat_sub_exact\n{finish}")
    # d ∣ N: one goal per divisor, each finished mechanically.
    for n, t in hyps:
        if re.match(r"^.+ ∣ .+$", t) and re.search(r"\d", t):
            out.append(f"divisor_cases {n} <;> ({primes.replace(chr(10), '; ')}{finish})" if primes
                       else f"divisor_cases {n} <;> {finish}")
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
    return [f"{BUDGET}\n{c}" if not c.startswith(("obtain", "subst", "by_contra", "have", "rcases")) else c
            for c in uniq[:LEAF_CAP]]
