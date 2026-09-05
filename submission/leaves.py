"""Leaf candidates: tactic blocks generated from the shape of a goal, tried by
Lean with no model asked. Measured on 3 September: the models found the routes
on rmo_2000_2, rmo_2001_2 and putnam_2018_a1 within minutes and lost the runs
on leaves of these shapes (ℕ subtraction under a bound, a perfect power between
consecutive powers, a bounded variable, the divisors of a product)."""
from __future__ import annotations

import math
import re

NUM = re.compile(r"^\d+$")
VAR = re.compile(r"^[A-Za-z_][\w']*$")
# Every alternative must close the goal: `simp_all` alone can rewrite a
# hypothesis, count as success, and leave the goal open (measured on the
# rmo_2001_2 case leaves). Cheap and specific first: the theorem's heartbeats
# are one budget, and a failing `nlinarith` ahead of the membership route spent
# it (putnam_2018_a1, v7.90); `simp_all <;> omega` is what closes a case whose
# second unknown is only linear after the case value is substituted.
MEMBERSHIP = ("Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, Finset.mem_insert, "
              "Finset.mem_singleton")
FINISH = (f"first | (simp only [{MEMBERSHIP}] at *; first | omega | (simp_all <;> omega))"
          " | omega | (norm_num at *; done) | nlinarith | (simp_all; done)"
          f" | (norm_num [{MEMBERSHIP}] at *; done) | (norm_num [{MEMBERSHIP}] at *; omega)")
LEAF_CAP = 6
CASES_MAX = 40
CYCLE_MAX = 24
# One check's elaboration is bounded: a candidate that does not finish fast is not one.
BUDGET = "set_option maxHeartbeats 400000 in"


def _hyps(goal_text: str) -> list[tuple[str, str]]:
    """Lean wraps a long type over indented continuation lines (and may end the
    `name :` line there); each hypothesis is read back as one line."""
    head = goal_text.split("⊢", 1)[0] if "⊢" in goal_text else ""
    lines: list[str] = []
    for line in head.split("\n"):
        if line[:1].isspace() and lines:
            lines[-1] += " " + line.strip()
        else:
            lines.append(line)
    out = []
    for line in lines:
        if line.startswith("case ") or " : " not in line:
            continue
        names, typ = line.split(" : ", 1)
        for n in names.split():
            out.append((n, " ".join(typ.split())))
    return out


def _target(goal_text: str) -> str:
    return " ".join(goal_text.rsplit("⊢", 1)[-1].split()) if "⊢" in goal_text else ""


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
    """`2 ≤ p` for every `Nat.Prime p` (the `prime_facts` elab, whatever the
    hypothesis is named): what omega and nlinarith need and a printed context
    never carries."""
    return "prime_facts\n" if _primes(hyps) else ""


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


def _finish(target: str, primes: list[str] = ()) -> str:
    """The closing chain; a disjunction also tries each disjunct; with two prime
    variables and numerals in the target, both bounded by the largest numeral
    and every pair tried (the (p-2)(q-2) = 9 case of rmo_2001_2)."""
    chain = FINISH
    if "∨" in target:
        chain += (" | (left; nlinarith) | (right; left; constructor <;> nlinarith)"
                  " | (right; right; constructor <;> nlinarith) | (right; nlinarith)")
    nums = [int(x) for x in re.findall(r"\b\d+\b", target)]
    if len(primes) == 2 and nums and max(nums) <= CASES_MAX:
        # Measured (image): with `p * q = 2p + 2q + 5` nlinarith bounds p only
        # once q = 2 is split off, the product (p - 2)(q - 3) ≥ 0 doing the rest.
        a, b, n = primes[0], primes[1], max(nums)
        # `:= (by ...)`: on one line a bare `by` would swallow the tactics after `;`.
        bound = lambda v, w: (f"have hb_{v} : {v} ≤ {n} := (by rcases Nat.lt_or_ge {w} 3 with h3 | h3 <;> "
                              f"[(interval_cases {w} <;> nlinarith); nlinarith])")
        chain += (f" | ({bound(a, b)}; {bound(b, a)}; interval_cases {a} <;> interval_cases {b} <;> "
                  f"first | omega | (norm_num at *; done) | (simp_all; done))")
    return chain


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


def _order(a: int, m: int) -> int | None:
    """The multiplicative order of a modulo m, or None when there is none or it is long."""
    if m < 2 or math.gcd(a, m) != 1:
        return None
    x, k = a % m, 1
    while x != 1 and k <= CYCLE_MAX:
        x, k = (x * a) % m, k + 1
    return k if x == 1 else None


def _cycles(goal_text: str) -> list[tuple[int, int, int, str]]:
    """(a, m, k, n) for every `a ^ n` with a literal base and a variable exponent
    over ℕ, m a modulus the goal mentions (`% m`, `m ∣`, `[MOD m]`), k the order."""
    nats = {n for n, t in _hyps(goal_text) if t == "ℕ"}
    mods = {int(m) for m in re.findall(r"% (\d+)\b|\b(\d+) ∣|\[MOD (\d+)\]", goal_text) for m in m if m}
    out = []
    for a, n in re.findall(r"\b(\d+) \^ ([A-Za-z_][\w']*)\b", goal_text):
        if n not in nats:
            continue
        # The modulus written against this power first (`a ^ n % m`, `m ∣ ... a ^ n`, `[MOD m]`).
        near = lambda m: not re.search(rf"{a} \^ {n}\b[^\n]*(% {m}\b|\[MOD {m}\])|\b{m} ∣ [^\n]*{a} \^ {n}\b", goal_text)
        for m in sorted(mods, key=lambda m: (near(m), m)):
            k = _order(int(a), m)
            if k and (int(a), m, k, n) not in out:
                out.append((int(a), m, k, n))
    return out


SUM_BOUND = re.compile(r"∑ [^,]*∈ Finset\.(?:range \((\w+) \+ 1\)|Icc 0 (\w+))")


def _sum_variables(hyps: list[tuple[str, str]], target: str) -> list[str]:
    """ℕ variables at which the target's sums end, when the target is an
    equation between two sums (the shape `sum_induct` handles)."""
    if " = " not in target or "∑" not in target or re.search(r"[∨∧↔→]", target):
        return []
    nat = {n for name, t in hyps if t.strip() == "ℕ" for n in name.split()}
    out: list[str] = []
    for m in SUM_BOUND.finditer(target):
        k = m.group(1) or m.group(2)
        if k in nat and k not in out:
            out.append(k)
    return out


from math import gcd as _gcd


def _dvd_bounds(hyps: list[tuple[str, str]]) -> str:
    """`have` lines: k ≤ v for every `h : k ∣ v` (k a numeral, v an identifier with
    a positivity fact in scope), and k₁k₂ ∣ v, k₁k₂ ≤ v for coprime pairs."""
    positive = {t.split("<", 1)[1].strip() for _, t in hyps if re.match(r"^0 < [A-Za-z_][\w']*$", t.strip())}
    positive |= {t.split(">", 1)[0].strip() for _, t in hyps if re.match(r"^[A-Za-z_][\w']* > 0$", t.strip())}
    divs: dict[str, list[tuple[int, str]]] = {}
    for n, t in hyps:
        m = re.match(r"^(\d+) ∣ ([A-Za-z_][\w']*)$", t.strip())
        if m and m.group(2) in positive:
            divs.setdefault(m.group(2), []).append((int(m.group(1)), n))
    lines: list[str] = []
    for v, ks in divs.items():
        for k, n in ks:
            lines.append(f"have hle_{n} : {k} ≤ {v} := Nat.le_of_dvd (by omega) {n}")
        for i in range(len(ks)):
            for j in range(i + 1, len(ks)):
                (k1, n1), (k2, n2) = ks[i], ks[j]
                if _gcd(k1, k2) == 1:
                    lines.append(f"have hdvd_{n1}_{n2} : {k1 * k2} ∣ {v} := "
                                 f"Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) {n1} {n2}")
                    lines.append(f"have hle_{n1}_{n2} : {k1 * k2} ≤ {v} := Nat.le_of_dvd (by omega) hdvd_{n1}_{n2}")
    return "\n".join(lines)


def _factorise(n: int) -> list[int]:
    """The distinct primes of n, ascending."""
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def _radical_bound(hyps: list[tuple[str, str]], rel: str, c: str, product: str) -> str | None:
    """`c ≤ P` (or `c ∣ P`), P a product of at most two atoms, from `h : m ∣ E`, E a
    product of powers of the same atoms: every prime of m to the bases, coprime
    product, `Nat.le_of_dvd`. Needs rad(m) ≥ c (or c ∣ rad(m))."""
    atoms = [t.strip() for t in product.split(" * ")]
    c = re.sub(r"^\((\d+) : ℕ\)$", r"\1", c)
    if not (1 <= len(atoms) <= 2 and all(VAR.match(a) for a in atoms) and NUM.match(c)):
        return None
    factor = r"([A-Za-z_][\w']*)(?: \^ (?:\d+|\(\d+ : ℕ\)))?"
    for name, t in hyps:
        m = re.match(rf"^(?:\((\d+) : ℕ\)|(\d+)) ∣ ((?:{factor})(?: \* (?:{factor}))*)$", t)
        if not m:
            continue
        bases = [b for b in re.findall(rf"(?:^| \* ){factor}", m.group(3))]
        if sorted(bases) != sorted(atoms):
            continue
        primes = _factorise(int(m.group(1) or m.group(2)))
        radical = 1
        for q in primes:
            radical *= q
        if rel == "∣" and radical % int(c) != 0 or rel == "≤" and radical < int(c):
            continue
        if rel == "∣":
            primes = [q for q in primes if int(c) % q == 0]
            radical = int(c)
        lines = [f"have hp{q} : {q} ∣ {product} := (by prime_to_bases {q} {name})" for q in primes]
        acc, last = primes[0], f"hp{primes[0]}"
        for q in primes[1:]:
            acc *= q
            nxt = f"hp{acc}" if acc != radical else "hrad"
            lines.append(f"have {nxt} : {acc} ∣ {product} := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) {last} hp{q}")
            last = nxt
        if last != "hrad":
            lines.append(f"have hrad : {radical} ∣ {product} := {last}")
        lines.append("exact hrad" if rel == "∣"
                     else "exact le_trans (by norm_num) (Nat.le_of_dvd (by positivity) hrad)")
        return "\n".join(lines)
    return None


def _over_int(hyps: list[tuple[str, str]], expr: str) -> bool:
    """Whether a variable of the expression is declared `ℤ`."""
    ints = {v for names, t in hyps if t == "ℤ" for v in names.split()}
    return any(v in ints for v in re.findall(r"[A-Za-z_][\w']*", expr))


def _nonlinear(hyps: list[tuple[str, str]], keep: str) -> list[str]:
    """Hypotheses (other than `keep`) with a product of two non-numeral terms."""
    out = []
    for n, t in hyps:
        if n != keep and re.search(r"[\w')]\s\*\s[A-Za-z_(]", t) and len(set(re.findall(r"\b[a-z]\w*\b", t))) >= 2:
            out.append(n)
    return out


BLOCKS = re.compile(r"∑ \w+ ∈ Finset\.Ico \S+ \((\w+) \+ 1\), ∑ \w+ ∈ Finset\.Ico ")

FACTOR = r"\((?:[^()]|\([^()]*\))+\)|[A-Za-z_][\w']*"


SET_FORALL = re.compile(r"^∀ (\w+) ∈ \{(\w+) \| ∃ ([\w ]+?), (.+)\}, (.+)$")
LOWER_BOUNDS = re.compile(r"^(.+?) ∈ lowerBounds \{(\w+) \| ∃ ([\w ]+?), (.+)\}$")


def _conjuncts(prop: str) -> list[str]:
    """Top-level `∧` parts of a proposition."""
    depth, parts, cur = 0, [], ""
    i = 0
    while i < len(prop):
        ch = prop[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if depth == 0 and prop.startswith(" ∧ ", i):
            parts.append(cur.strip())
            cur, i = "", i + 3
            continue
        cur += ch
        i += 1
    parts.append(cur.strip())
    return parts


def _destructured(goal_text: str) -> list[tuple[str, str]]:
    """(prefix, inner goal): `∀ n ∈ {n | ∃ a b, P ∧ …}, T` (or `c ∈ lowerBounds {…}`)
    introduced and destructured, a hypothesis `P ∧ Q` split. Measured on rmo_2000_6
    (frame129): the inner leaf was accepted 4 times, then failed 4 times on these."""
    hyps, target = _hyps(goal_text), _target(goal_text)
    head = goal_text.split("⊢", 1)[0] if "⊢" in goal_text else ""
    out: list[tuple[str, str]] = []
    m = SET_FORALL.match(target) or LOWER_BOUNDS.match(target)
    if m:
        if m.re is SET_FORALL:
            n, bound, exist, body, inner = m.groups()
        else:
            c, bound, exist, body = m.groups()
            n, inner = "n", f"{c} ≤ n"
        body = re.sub(rf"(?<![\w'.]){re.escape(bound)}(?![\w'])", n, body) if bound != n else body
        parts = _conjuncts(body)
        names = [f"vm_c{i}" for i in range(len(parts))]
        binders = " ".join([n] + exist.split())
        text = (head + f"{binders} : ℕ\n" + "".join(f"{h} : {t}\n" for h, t in zip(names, parts))
                + f"⊢ {inner}")
        out.append((f"intro {n} vm_hn\nobtain ⟨{', '.join(exist.split() + names)}⟩ := vm_hn", text))
    for h, t in hyps:
        parts = _conjuncts(t)
        if len(parts) > 1 and not t.startswith(("∀", "∃")):
            names = [f"vm_{h}{i}" for i in range(len(parts))]
            rest = [l for l in head.split("\n") if not l.startswith(f"{h} :")]
            text = "\n".join(rest).rstrip("\n") + "\n" + "".join(f"{a} : {b}\n" for a, b in zip(names, parts)) + f"⊢ {target}"
            out.append((f"obtain ⟨{', '.join(names)}⟩ := {h}", text))
            break
    return out


def leaf_candidates(goal_text: str) -> list[str]:
    hyps = _hyps(goal_text)
    target = _target(goal_text)
    for prefix, inner in _destructured(goal_text):
        got = [f"{prefix}\n{c[len(BUDGET) + 2:-1].replace('; ', chr(10))}" for c in leaf_candidates(inner)]
        if got:
            return _finalised(got)
    bounds = _bounds(hyps)
    powers = _powers(hyps)
    primes = _prime_facts(hyps)
    prime_vars = [t.split()[-1] for n, t in hyps if n in _primes(hyps)]
    finish = _finish(target, prime_vars)
    # The tightest bounds first; `0 < v` carries nothing a subtraction needs.
    lowers = sorted(((n, v, c) for n, v, kind, c in bounds if kind == "lower" and c >= 2),
                    key=lambda b: -b[2])
    out: list[str] = []

    # a ^ n under a modulus, a and the modulus numerals: the residue cycles with
    # period k, so n % k decides every claim. Measured on p09 (v7.91–v7.93):
    # `2 ^ n % 7 = 1` was the step withdrawn after four tries in every failing run.
    for a, m, k, n in _cycles(goal_text):
        out.append(f"pow_cycle {a} {m} {k} {n}")

    # An identity between sums whose ranges end at a variable: induction on it,
    # the step mechanical (peels, rescaling, Pascal, omega). Measured on
    # putnam_2020_a2's generalisation ∑_{j≤m} 2^(m-j) C(n+j,j) = ∑_{i≤m} C(n+m+1,i):
    # both models withdrew the Pascal step; the recipe closes it in 0.5 s.
    for k in _sum_variables(hyps, target):
        out.append(f"sum_induct {k}")
    # `c ≤ E` from `h : c ∣ E` and E > 0. Measured on rmo_2000_6 (frame117):
    # `⊢ 10 ≤ a * b` under `h10 : 10 ∣ a * b` was reported 333 times in one run.
    le = re.match(r"^(.+?) ≤ (.+)$", target)
    ge = re.match(r"^(.+?) ≥ (.+)$", target)
    lo, hi = (le.group(1), le.group(2)) if le else ((ge.group(2), ge.group(1)) if ge else (None, None))
    if lo is not None:
        for n, t in hyps:
            if t.strip() == f"{lo} ∣ {hi}".strip():
                out.append(f"exact Nat.le_of_dvd (by positivity) {n}")
                out.append(f"exact Nat.le_of_dvd (by omega) {n}")
                out.append(f"exact Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) {n}")
        # Bounds from divisibility by numerals: `k ∣ v` gives `k ≤ v`, two coprime
        # divisors give their product, then nlinarith over the products. Measured
        # on rmo_2000_6: `⊢ 10 ≤ a * b` under `2 ∣ a`, `5 ∣ a` (or `5 ∣ b`).
        facts = _dvd_bounds(hyps)
        if facts and NUM.match(lo.strip()):
            out.append(facts + "\nfirst | omega | nlinarith")
        # `c ≤ a * b` from `m ∣ a ^ i * b ^ j`, rad(m) ≥ c. Measured on rmo_2000_6
        # (frame117/119): the leaf every failing run died on, 6 model tries each.
        radical = _radical_bound(hyps, "≤", lo.strip(), hi.strip())
        if radical:
            out.append(radical)
        # The same through `hn : n = a * b` (measured on rmo_2000_6: `⊢ 10 ≤ n`).
        for n, t in hyps:
            m = re.match(rf"^{re.escape(hi.strip())} = ([A-Za-z_][\w']*(?: \* [A-Za-z_][\w']*)?)$", t)
            if m and VAR.match(hi.strip()):
                radical = _radical_bound(hyps, "≤", lo.strip(), m.group(1))
                if radical:
                    out.append(f"subst {n}\n{radical}")
    dv = re.match(r"^(?:\((\d+) : ℕ\)|(\d+)) ∣ (.+)$", target)
    if dv:
        radical = _radical_bound(hyps, "∣", dv.group(1) or dv.group(2), dv.group(3))
        if radical:
            out.append(radical)
    # ∑_{i ∈ Ico A B} x i / i ≤ R for x positive and antitone: the lemma bounds the
    # block by its length times its first term, the rest is one division
    # inequality. Measured on rmo_2000_3 (cells build, 0/2): the models stated
    # this bound and withdrew it after 4 tries every time.
    blk = re.match(r"^∑ (\w+) ∈ Finset\.Ico (\S+|\([^()]*\)) (\S+|\([^()]*(?:\([^()]*\)[^()]*)*\)), "
                   r"([A-Za-z_][\w']*) \1 / (?:↑\1|\(\1 : ℝ\)) ≤ (.+)$", target)
    if blk:
        _, a, b, x, _ = blk.groups()
        pos = next((n for n, t in hyps if re.match(rf"^∀ (?:\w+|\(\w+ : ℕ\)), 0 < {re.escape(x)} \w+$", t)), None)
        anti = next((n for n, t in hyps if t == f"Antitone {x}"), None)
        mono = next((n for n, t in hyps if re.match(rf"^∀ (?:\w+|\(\w+ : ℕ\)), (?:{re.escape(x)} \w+ ≥ {re.escape(x)} \(\w+ \+ 1\)"
                                                     rf"|{re.escape(x)} \(\w+ \+ 1\) ≤ {re.escape(x)} \w+)$", t)), None)
        if pos and (anti or mono):
            lines = [] if anti else [f"have hanti : Antitone {x} := antitone_nat_of_succ_le (fun n => {mono} n)"]
            anti = anti or "hanti"
            lines.append(f"refine le_trans (vm_sum_div_block {x} {pos} {anti} {a} {b} "
                         f"(by first | positivity | omega | nlinarith)) ?_")
            lines.append(f"have hle : {a} ≤ {b} := (by first | omega | nlinarith)")
            lines.append("rw [Nat.cast_sub hle]; push_cast")
            nat_vars = {v for names, t in hyps if t == "ℕ" for v in names.split()}
            for v in sorted(set(re.findall(r"[A-Za-z_][\w']*", a)) & nat_vars):
                low = next((n for n, t in hyps if t in (f"1 ≤ {v}", f"0 < {v}", f"{v} ≥ 1", f"{v} > 0")), None)
                if low:
                    lines.append(f"have h{v}0 : ({v} : ℝ) ≠ 0 := (by exact_mod_cast (by omega : {v} ≠ 0))")
                    lines.append(f"have h{v}r : (1 : ℝ) ≤ {v} := (by exact_mod_cast {low})")
            lines.append(f"have hxp := {pos} {a}")
            lines.append("first | (rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith) "
                         "| (field_simp; rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith) "
                         "| (field_simp; nlinarith)")
            out.append("\n".join(lines))
    # Blocks [g j, g (j+1)) telescoping over j < m + 1: rmo_2000_3's decomposition
    # of ∑_{i<(m+1)²} into the sums over [j², (j+1)²).
    m = BLOCKS.search(target)
    if m and m.group(1) in {n for name, t in hyps if t.strip() == "ℕ" for n in name.split()}:
        out.append(f"ico_blocks {m.group(1)}")

    # v ^ n bounded by powers in the context (on v ^ n itself, or through
    # `v ^ n = P`), the goal about v: the bounds move to v, then omega. Measured
    # on rmo_2000_2 (v7.79): the route left `h_low : (x+2)^3 ≤ P`, `h_up : P ≤
    # (x+3)^3`, `h : y^3 = P ⊢ y = x + 2 ∨ y = x + 3`, and no model closed it.
    for _, v, n, _ in _powered(hyps):
        if re.search(rf"\b{re.escape(v)}\b", target) and any(
                re.search(r"(≤|<)", t) and re.search(r"\^ " + n + r"\b", t) for _, t in hyps):
            out.append(f"pow_bounds {v} {n}")

    # `x = c` (and `y = d`) asked outright, with `h : y ^ n = P(x)`: x ≤ c by the
    # squeeze at the large-x shift, c ≤ x by the squeeze one shift lower (the ℕ
    # subtraction in P made exact first), then y from y ^ n = numeral. Measured on
    # rmo_2000_2 (frame116, 0/1): the models spent 40 min on `2x(x-9)` over ℕ; 4.2 s.
    sol = re.match(r"^([A-Za-z_][\w']*) = (\d+)(?: ∧ ([A-Za-z_][\w']*) = (\d+))?$", target)
    if sol:
        v, c, w, d = sol.group(1), sol.group(2), sol.group(3), sol.group(4)
        for hn, y, n, rhs in powers:
            shifts = _shifts(rhs, int(n))
            if not shifts or y == v or not re.search(rf"\b{re.escape(v)}\b", rhs) or (w and w != y):
                continue
            hi = shifts[0]
            k = int(hi.split("+")[1]) if "+" in hi else 0
            lo = f"{v} + {k - 1}" if k > 1 else v
            exact = "nat_sub_exact; " if " - " in rhs else ""
            lines = (f"have hle : {v} ≤ {c} := (by by_contra hc; push_neg at hc; "
                     f"pow_squeeze {y} {n} ({hi}) with hc)\n"
                     f"have hge : {c} ≤ {v} := (by by_contra hc; push_neg at hc; {exact}"
                     f"pow_squeeze {y} {n} ({lo}))\n")
            if w:
                lines += (f"have hv : {v} = {c} := (by omega)\nsubst hv\nnorm_num at {hn} ⊢\n"
                          f"first | done | omega | (pow_squeeze {y} {n} {d}) | nlinarith")
            else:
                lines += "omega"
            out.append(lines)
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
            out.append(f"rcases Nat.lt_or_ge {x} {t} with hlt | hge <;> "
                       f"[(interval_cases {x} <;> first | omega | (bounded_cases {y} {root})); "
                       f"(obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hge; subst hk; "
                       f"first | omega | nlinarith | (ring_nf at *; omega) | (ring_nf at *; nlinarith))]")
            break
    # A variable defined by an equation `w = E`: substitute, make ℕ subtraction
    # exact, then arithmetic. Measured on rmo_2000_2: `hyx : y = x + 2 ⊢ x = 9`.
    for hn, t in hyps:
        d = re.match(r"^([A-Za-z_][\w']*) = (.+)$", t)
        if d and not NUM.match(d.group(2).strip()) and re.search(r"[A-Za-z]", d.group(2)) \
                and not re.search(r"[∨∧↔→∀∃∣]", t) and not re.search(r"[↔→∀∃∣]", goal_text):
            out.append(f"{primes}subst {hn}\n{'nat_sub_exact' + chr(10) if '-' in goal_text else ''}"
                       + finish)
            break
    # A variable defined through ℕ subtraction, `m - p - q = D`: solve for it and
    # substitute. Measured on rmo_2001_2 (v7.79): divisor_cases left eight such
    # cases and every model reply on them failed at the truncated subtraction.
    if _solved_subtractions(hyps) and not re.search(r"[↔→∀∃]", target):
        out.append(f"{primes}solve_sub\n{finish}")
    # A disjunction of such equations (what divisor_cases leaves as a fact):
    # every case at once, the same block in each. Measured on rmo_2001_2
    # (v7.87): the eight-way fact was on the board four times and the models
    # never split it inside the clock.
    for hn, t in hyps:
        cases = [c.strip() for c in t.split(" ∨ ")]
        if len(cases) < 2 or not re.search(r"[∨]", t) or re.search(r"[↔→∀∃]", target):
            continue
        # `v = c₁ ∨ v = c₂ ∨ ...`, c closed: substitute each and finish. Measured
        # on putnam_2018_a1 (v7.88): divisor_cases over ℤ left `a = 673 ∨ ...`
        # and `b = 1358114 ∨ ...` with the membership goal open.
        plain = [re.match(r"^([A-Za-z_][\w']*) = ([^A-Za-z_]+)$", c) for c in cases]
        if all(plain) and len({h.group(1) for h in plain}) == 1:
            out.append(f"rcases {hn} with {' | '.join(['rfl'] * len(cases))} <;> ({finish})")
            break
        heads = [re.match(r"^([A-Za-z_][\w']*)((?: - [^-=()]+)+) = (.+)$", c) for c in cases]
        if not all(heads) or len({(h.group(1), h.group(2)) for h in heads}) != 1:
            continue
        alts = " | ".join(["hc"] * len(cases))
        out.append(f"{primes}rcases {hn} with {alts} <;> (solve_sub; {finish})")
        break
    if "-" in goal_text and not re.search(r"[↔→∀∃∣]", target):
        out.append(f"{primes}nat_sub_exact\n{finish}")
    # d ∣ N: one goal per divisor, each finished mechanically.
    for n, t in hyps:
        if re.match(r"^.+ ∣ .+$", t) and re.search(r"\d", t):
            out.append(f"{primes}divisor_cases {n} <;> (first | (solve_sub; {finish}) | ({finish}))")
    # A * B = N gives A ∣ N and B ∣ N without a model step. Measured on the
    # v7.93 repeats: the pass on each problem had the model write the `∣`
    # fact, the failure had only the product on the board.
    for n, t in hyps:
        # A factor may hold one level of brackets: `(m - (p + q))` was how the
        # models wrote it on rmo_2001_2 (measured, cells build: the leaf never fired).
        m = re.match(rf"^({FACTOR}) \* ({FACTOR}) = (.+)$", t)
        if not m or not re.search(r"\d", m.group(3)) or re.search(r"[∨∧↔→∀∃]", t):
            continue
        for factor, intro in ((m.group(1), "Dvd.intro"), (m.group(2), "Dvd.intro_left")):
            factor = factor[1:-1] if factor.startswith("(") else factor
            # Over ℤ each case has `hx : factor = ±d`: the product equation is
            # rewritten by it and the other nonlinear facts cleared (measured on
            # putnam_2018_a1: with `h_eq : 2018 * (b + a) = a * b * 3` in scope
            # omega spent 400000 heartbeats; without it the 18 cases take 3.7 s).
            if _over_int(hyps, factor):
                clears = " ".join(_nonlinear(hyps, keep=n))
                out.append(f"{primes}have hdvd : {factor} ∣ {m.group(3)} := {intro} _ {n}; "
                           f"divisor_cases hdvd <;> (clear hm hdvd {clears}; "
                           f"(try simp only [{MEMBERSHIP}] at *); rw [hx] at {n}; norm_num at {n} <;> omega)")
            out.append(f"{primes}have hdvd : {factor} ∣ {m.group(3)} := {intro} _ {n}; "
                       f"divisor_cases hdvd <;> (first | (solve_sub; {finish}) | ({finish}))")
    # `p² + k·pq + q² = m²` (k > 2): (m - p - q)(m + p + q) = (k-2)pq, so m - p - q
    # divides a product of primes and the divisor leaf takes over. Measured on
    # rmo_2001_2 (frame119): the passes had these two facts written by a model,
    # the failures wrote the 8-way disjunction instead and withdrew it 4 times.
    for hn, t in hyps:
        m = (re.match(r"^([A-Za-z_][\w']*) \^ 2 \+ (\d+) \* \1 \* ([A-Za-z_][\w']*) \+ \3 \^ 2 = ([A-Za-z_][\w']*) \^ 2$", t)
             or re.match(r"^([A-Za-z_][\w']*) \^ 2 = ([A-Za-z_][\w']*) \^ 2 \+ (\d+) \* \2 \* ([A-Za-z_][\w']*) \+ \4 \^ 2$", t))
        if not m:
            continue
        p, k, q, mm = (m.group(1), m.group(2), m.group(3), m.group(4)) if " = " + m.group(4) + " ^ 2" in t \
            else (m.group(2), m.group(3), m.group(4), m.group(1))
        c = int(k) - 2
        if c < 1:
            continue
        two_le = ", ".join(f"Nat.Prime.two_le {n}" for n in _primes(hyps))
        out.append(
            f"have hle : {p} + {q} ≤ {mm} := (by nlinarith [{two_le}])\n"
            f"have hfac : ({mm} - {p} - {q}) * ({mm} + {p} + {q}) = {c} * {p} * {q} := "
            f"(by obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle; subst hk; "
            f"have hk' : {p} + {q} + k - {p} - {q} = k := (by omega); rw [hk']; ring_nf at {hn} ⊢; omega)\n"
            f"have hdvd : {mm} - {p} - {q} ∣ {c} * {p} * {q} := Dvd.intro _ hfac; {primes}"
            f"divisor_cases hdvd <;> (first | (solve_sub; {finish}) | ({finish}))")
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
    return _finalised(out)


def _finalised(out: list[str]) -> list[str]:
    seen, uniq = set(), []
    for c in out:
        if c not in seen:
            seen.add(c)
            uniq.append(c)
    # One line each, the whole block under the heartbeat cap: `set_option ... in`
    # governs only the tactic that follows it, and a `first` alternative is a
    # tactic sequence, so the closing chain is always the last element.
    return [f"{BUDGET} ({'; '.join(l.strip() for l in c.split(chr(10)) if l.strip())})"
            for c in uniq[:LEAF_CAP]]
