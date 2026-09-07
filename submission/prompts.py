"""The text the models are sent: the two system prompts, the note a Lean
message earns, and the sheet a goal shape earns."""

from __future__ import annotations
import re


PLANNER_SYSTEM = """You are a competition mathematician. You are given one goal from a
Lean 4 proof, with its hypotheses.

Say how to prove it, in at most six short lines. Name the key fact: the modulus,
the witness, the identity, the bound, the induction, the case split. Give the
value when it is a number. Write mathematics, not Lean, and do not restate the
goal."""


FRAMEWORK_SYSTEM = """You extend a Lean 4 proof one step at a time, against a full Mathlib.

The file is complete and checkable at every moment. Every unproved place is
`sorry`, except exactly one, which is `skip`: that is the active goal. You are
asked for the next step at the `skip`, and nothing else.

A step does one of two things:
- it reshapes the goal: intro, induction ... with, constructor, refine, rcases,
  obtain, subst, left, right, exfalso, interval_cases, by_contra, show, rw.
  A reshaping step goes alone, because it changes the goal for everything after.
- it asserts a new fact: a `have`. Give every `have` a body. Independent `have`s
  may be sent together; Lean names each one that fails.

When no closer works, something is missing that the goal does not contain. It is
almost always a witness, a map into a smaller index set, a modulus, an algebraic
identity, a bound that traps a variable, a recurrence, or a case split. Name
which, state it as a `have`, and prove that. When the missing thing is a number,
do not guess it: ask for a `#eval` probe instead.

Rules:
- Never write a lemma name you have not seen Lean accept as a closing term.
  Write the goal and let `exact?` name it. This does not reach `rw` and `simp`
  arguments, which you must write from memory.
- State each fact as small as it can stand on its own.
- When a tactic has failed twice on one goal, restate the goal; do not retry it.
- Anything a later step names must be at the outer level, not inside another
  `have`'s body.
- Copy terms out of the printed goal rather than retyping them: omega and
  linarith atomise syntactically, so spellings must match.

`nlinarith` is the most expensive thing you can write. Measured: a proof of one
inequality that ended in `nlinarith` with three hints produced a 95,000-character
term, which the grader compiles and re-checks under a 180-second limit it failed.
The local check said 348ms, so nothing warns you. Cut the goal into `have`s small
enough for `linarith`, `positivity` or `norm_num`, and leave `nlinarith` for a
step that is already almost closed.

When more than one goal needs the same fact, state it once as a theorem of its
own instead of as a `have` inside one of them. Reply with

  theorem <a new name> <binders> : <statement> := by
    sorry

and it is placed above the graded theorems, where every goal can reach it. Its
`sorry` becomes the next cursor, so you prove it one step at a time like
anything else. A `have` proved inside one theorem is invisible to the others.

Do not open a `·` bullet you cannot close in the same step: a bullet whose
interior is unfinished is an error, not a placeholder. A step that splits the
goal is complete on its own; each goal it opens gets its own turn.

Your reply has a token limit. Measured on p09: a reply that reasoned in prose
and then wrote a whole proof hit the limit and the code block was cut in half,
so none of it could be used and Lean reported a syntax error that was not the
mistake. Write the next step and stop.

Answer with Lean tactic lines only. No prose, no code fences, no theorem
header, no `native_decide`, and no `sorry` except as the body of a new theorem
you are introducing. Indent as if at the top level of the
proof; branches of an `induction ... with` end in `sorry` where you have not
worked yet."""


# Added to the prompt: what Lean's message does not say. Sent only when
# the message that triggers it appears, which keeps the prompt small.
NOTES: tuple[tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"omega could not"),
     "omega atomises syntactically, so (3*a)^2 and 9*a^2 are different atoms: "
     "state the ring identity as its own `have ... := by ring`. omega also does "
     "not instantiate a quantified fact; apply it yourself first."),
    (re.compile(r"linarith failed"),
     "Every closer before nlinarith is linear or syntactic. For a symmetric "
     "inequality in nonnegative variables the hint is each square times the "
     "variable its difference leaves out: `have : 0 ≤ a * (b - c) ^ 2 := by "
     "positivity`, which needs 0 ≤ a in context. Over ℕ this is vacuous, "
     "because b - c is truncated."),
    (re.compile(r"maximum number of heartbeats"),
     "This is Lean's elaboration budget, not wall clock. Make the step cheaper, "
     "or ask for `set_option maxHeartbeats 400000 in` before the theorem."),
    (re.compile(r"exact\? could not"),
     "exact? only produces closing terms. It will not give you a rw, simp or "
     "refine argument; write those from memory."),
    (re.compile(r"unknown (identifier|constant)|environment does not contain"),
     "The name is wrong or out of scope. Drop it and state the fact you wanted "
     "as a `have`, letting exact? name the lemma."),
    (re.compile(r"simp made no progress"),
     "Membership in a literal Finset opens with `simp only [Finset.mem_insert, "
     "Finset.mem_singleton]`, in a literal Set with `simp only "
     "[Set.mem_insert_iff, Set.mem_singleton_iff]`. The namespaces do not "
     "interchange."),
    (re.compile(r"motive is not type correct|induction"),
     "rcases on an inductively defined Prop loses the induction hypothesis. Use "
     "`induction h with | c₁ ... | c₂ ...`, labelled by constructor name, and "
     "clear hypotheses mentioning the variable first."),
    (re.compile(r"unexpected token '(,|have|with|in)'; expected (command|',')"),
     "The parser left the proof on the line before, which is what Lean 3 "
     "spellings do here: no comma at the end of a tactic line, `obtain ⟨a, b⟩ "
     ":= h` for `cases h with a b`, `∑ x ∈ s` for `∑ x in s`, and every line of "
     "one block at one indentation."),
    (re.compile(r"unexpected token '!'"),
     "`n !` is `Nat.factorial` notation that `open Nat` provides and this file "
     "does not have. Write `Nat.factorial n` or `n.factorial`."),
    (re.compile(r"ℕ|Nat\.sub"),
     "ℕ subtraction is truncated. State `b ≤ a` as its own `have` and let omega "
     "move the term across, or move to ℤ. Under `h : a ≤ x`, `obtain ⟨k, rfl⟩ := "
     "Nat.exists_eq_add_of_le h` replaces x by a + k everywhere, after which "
     "`ring_nf at *; omega` or `nlinarith` sees no subtraction; `cases x` does not."),
)


# Added to the prompt: the names the loaded Mathlib has, given before
# the first step to any goal whose vocabulary they fit. Every name and signature
# below was printed by `#check` in the harness image; nothing is from memory.
SHEETS: tuple[tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"IsLeast|IsGreatest|lowerBounds|upperBounds"),
     "IsLeast S a is a ∈ S ∧ a ∈ lowerBounds S: `refine ⟨?_, ?_⟩`. Membership in a set-builder is its existential: `exact ⟨w₁, w₂, by norm_num, by norm_num, by decide, rfl⟩`.\n"
     "The bound: `intro n hn` then `obtain ⟨a, b, ha, hb, h, rfl⟩ := hn` (Set.mem_setOf_eq). IsGreatest is the mirror with upperBounds."),
    (re.compile(r"∣"),
     "Nat.Prime.dvd_mul (hp : p.Prime) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n\n"
     "Nat.Prime.dvd_of_dvd_pow (hp : p.Prime) : p ∣ m ^ n → p ∣ m ; Nat.dvd_of_pow_dvd : 1 ≤ k → p ^ k ∣ m → p ∣ m\n"
     "Nat.Coprime.mul_dvd_of_dvd_of_dvd : m.Coprime n → m ∣ a → n ∣ a → m * n ∣ a (omega also gets 10 ∣ x from 2 ∣ x and 5 ∣ x)\n"
     "Nat.le_of_dvd : 0 < n → m ∣ n → m ≤ n ; Nat.dvd_antisymm ; Nat.Prime.eq_one_or_self_of_dvd (hp) (m) : m ∣ p → m = 1 ∨ m = p\n"
     "Nat.dvd_sub : k ∣ m → k ∣ n → k ∣ m - n ; Nat.dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c ; Nat.pow_dvd_pow_iff_le_right : 1 < x → (x ^ k ∣ x ^ l ↔ k ≤ l)\n"
     "Nat.Prime.pow_dvd_iff_le_factorization (hp) (hn : n ≠ 0) : p ^ k ∣ n ↔ k ≤ n.factorization p. Prefer the route through a prime dividing a factor; factorization arithmetic needs nonzero side goals at every step.\n"
     "A closed fact such as 2000 ∣ 5 ^ 3 * 2 ^ 4 is `by decide` or `by norm_num`.\n"
     "d ∣ N with N a numeral or a product of primes (ℕ or ℤ): `divisor_cases h` (a tactic defined in this file) gives one goal per divisor; never decide the divisor set of a large numeral (measured at 4072324: recursion depth and heartbeats blow up)."),
    (re.compile(r"divisors"),
     "Nat.mem_divisors : n ∈ m.divisors ↔ n ∣ m ∧ m ≠ 0 ; Nat.Prime.divisors (hp) : p.divisors = {1, p}\n"
     "Nat.divisors_mul (m n) : (m * n).divisors = m.divisors * n.divisors (pointwise product, no coprimality needed; Finset.mem_mul)\n"
     "Nat.divisors_prime_pow (hp) (k) : (p ^ k).divisors = (Finset.range (k + 1)).map ⟨(p ^ ·), _⟩ ; Nat.dvd_prime_pow (hp) : i ∣ p ^ m ↔ ∃ k ≤ m, i = p ^ k\n"
     "Nat.dvd_mul : k ∣ m * n ↔ ∃ k₁ k₂, k₁ ∣ m ∧ k₂ ∣ n ∧ k₁ * k₂ = k. For a 7-digit n, `decide` on n.divisors does not finish; go through its prime factorisation."),
    (re.compile(r"%|≡|ModEq"),
     "Nat.pow_mod (a b n) : a ^ b % n = (a % n) ^ b % n ; Nat.mul_mod ; Nat.add_mod ; Nat.mod_mod_of_dvd (a) : c ∣ b → a % b % c = a % c\n"
     "Nat.mod_lt (x) : 0 < y → x % y < y ; Nat.div_add_mod (m n) : n * (m / n) + m % n = m ; Nat.mod_two_eq_zero_or_one (n)\n"
     "Nat.even_iff : Even n ↔ n % 2 = 0 ; Nat.odd_iff ; Nat.ModEq.pow (m) : a ≡ b [MOD n] → a ^ m ≡ b ^ m [MOD n]\n"
     "omega decides linear facts with % and / by constants. A residue split: `have h := Nat.mod_lt n (by norm_num : 0 < 9)`, `generalize n % 9 = r at *`, `interval_cases r`."),
    (re.compile(r"∑|∏|Finset\.sum|Finset\.prod"),
     "Finset.sum_range_succ (f n) : ∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n ; Finset.prod_range_succ ; Finset.sum_range_zero\n"
     "Finset.sum_range_id (n) : ∑ i ∈ range n, i = n * (n - 1) / 2 ; Finset.sum_range_id_mul_two (n) : (∑ i ∈ range n, i) * 2 = n * (n - 1)\n"
     "Finset.mul_sum (s f a) : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i ; Finset.sum_mul ; Finset.sum_add_distrib ; Finset.sum_const (b) : ∑ _x ∈ s, b = s.card • b ; Finset.card_range\n"
     "Finset.sum_le_sum : (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i ; Finset.sum_congr rfl (fun i hi => _)\n"
     "A closed form: `induction n with | zero => simp | succ n ih => rw [Finset.sum_range_succ, ih]; ring` (over ℕ prove the form without division first). Spell it ∑ x ∈ s, not ∑ x in s."),
    (re.compile(r"factorial|!"),
     "Nat.factorial_succ (n) : (n + 1).factorial = (n + 1) * n.factorial ; Nat.factorial_pos ; Nat.factorial_le : m ≤ n → m.factorial ≤ n.factorial\n"
     "Nat.dvd_factorial : 0 < m → m ≤ n → m ∣ n.factorial ; Nat.Prime.dvd_factorial (hp) : p ∣ n.factorial ↔ p ≤ n\n"
     "Write Nat.factorial n or n.factorial (the ! notation needs `open Nat`); small values evaluate with `decide` or `norm_num [Nat.factorial]`."),
    (re.compile(r"\^[^∧∨,]*[<≤]|[<≤][^∧∨,]*\^"),
     "Nat.pow_lt_pow_left : a < b → n ≠ 0 → a ^ n < b ^ n ; Nat.pow_le_pow_left : a ≤ b → ∀ i, a ^ i ≤ b ^ i\n"
     "Nat.pow_lt_pow_right : 1 < a → m < n → a ^ m < a ^ n ; Nat.pow_le_pow_right : a > 0 → i ≤ j → a ^ i ≤ a ^ j ; Nat.lt_pow_self : 1 < a → n < a ^ n\n"
     "Nat.pow_lt_pow_iff_left : n ≠ 0 → (a ^ n < b ^ n ↔ a < b) ; Nat.pow_le_pow_iff_left ; Nat.pow_left_injective : n ≠ 0 → Function.Injective (· ^ n) ; Nat.mul_self_le_mul_self_iff : m * m ≤ n * n ↔ m ≤ n\n"
     "Over ℤ or ℝ: pow_le_pow_left₀ : 0 ≤ a → a ≤ b → ∀ n, a ^ n ≤ b ^ n ; lt_of_pow_lt_pow_left₀ (n) : 0 ≤ b → a ^ n < b ^ n → a < b ; sq_nonneg a\n"
     "To pin an unknown: squeeze it between consecutive powers with nlinarith (`(x + 2) ^ 3 < y ^ 3`, `y ^ 3 < (x + 3) ^ 3`), convert with Nat.pow_lt_pow_iff_left, then omega or interval_cases."),
    (re.compile(r"factorization"),
     "Nat.factorization_mul : a ≠ 0 → b ≠ 0 → (a * b).factorization = a.factorization + b.factorization ; Nat.factorization_pow (n k) : (n ^ k).factorization = k • n.factorization\n"
     "Nat.Prime.factorization_self (hp) : p.factorization p = 1 ; Nat.factorization_eq_zero_of_not_dvd : ¬p ∣ n → n.factorization p = 0 ; Nat.eq_of_factorization_eq"),
    (re.compile(r"ℤ|ℚ|Int\.|Rat\.|\(↑|natAbs"),
     "Over ℚ clear denominators first: `field_simp at h ⊢` (needs `(a : ℚ) ≠ 0` facts: `by positivity` or `by exact_mod_cast ha.ne'`), then `norm_cast at h` (or `push_cast`) to land in ℤ, then `nlinarith`/`omega`.\n"
     "div_add_div (a c) (hb : b ≠ 0) (hd : d ≠ 0) : a / b + c / d = (a * d + b * c) / (b * d) ; div_eq_div_iff (hb) (hd) : a / b = c / d ↔ a * d = c * b\n"
     "Int.le_of_dvd : 0 < b → a ∣ b → a ≤ b ; Int.natAbs_dvd_natAbs : a.natAbs ∣ b.natAbs ↔ a ∣ b ; Int.natAbs_mul ; Int.natAbs_pow ; Int.natAbs_of_nonneg : 0 ≤ a → ↑a.natAbs = a ; Int.toNat_of_nonneg\n"
     "Int.emod_emod_of_dvd (n) : m ∣ k → n % k % m = n % m ; Int.emod_two_eq_zero_or_one (n). An equation over ℤ with bounded unknowns: bound them, `interval_cases`, `omega`/`decide`.\n"
     "Membership in a literal set: `simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]` then `omega`; the ↔ splits with `constructor` and each direction `rintro` / `rcases h with h | h | h`."),
    (re.compile(r"choose|Icc|Ico"),
     "Nat.choose_succ_succ (n k) : (n+1).choose (k+1) = n.choose k + n.choose (k+1) ; Nat.choose_zero_right ; Nat.choose_self ; Nat.sum_range_choose (n) : ∑ m ∈ range (n + 1), n.choose m = 2 ^ n\n"
     "Nat.choose_mul_succ_eq (n k) : n.choose k * (n + 1) = (n + 1).choose k * (n + 1 - k) ; Nat.succ_mul_choose_eq (n k) : (n+1) * n.choose k = (n+1).choose (k+1) * (k+1)\n"
     "Finset.sum_Icc_succ_top (h : a ≤ b + 1) (f) : ∑ k ∈ Icc a (b + 1), f k = ∑ k ∈ Icc a b, f k + f (b + 1) ; Finset.sum_Ico_succ_top (h : a ≤ b) (f) : ∑ k ∈ Ico a (b + 1), f k = ∑ k ∈ Ico a b, f k + f b\n"
     "Finset.sum_Ico_consecutive (f) : m ≤ n → n ≤ k → ∑ i ∈ Ico m n, f i + ∑ i ∈ Ico n k, f i = ∑ i ∈ Ico m k, f i ; Finset.sum_Ico_eq_sum_range (f m n) : ∑ k ∈ Ico m n, f k = ∑ k ∈ range (n - m), f (m + k) ; Finset.range_eq_Ico\n"
     "Finset.mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b ; Finset.mem_Ico ; Finset.mem_range ; Finset.sum_comm ; Finset.sum_range_succ_comm. An identity in k over a sum: `induction k with | zero => simp | succ k ih => …` and strengthen the statement if the step needs more than ih."),
    (re.compile(r"ℝ|Real\.|/ ↑|/ \(↑"),
     "one_div_le_one_div_of_le : 0 < a → a ≤ b → 1 / b ≤ 1 / a ; div_le_div_of_nonneg_left : 0 ≤ a → 0 < c → c ≤ b → a / b ≤ a / c ; div_le_div_iff_of_pos_right : 0 < c → (a / c ≤ b / c ↔ a ≤ b)\n"
     "Finset.sum_le_sum : (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i ; Finset.sum_le_card_nsmul (s f n) : (∀ x ∈ s, f x ≤ n) → s.sum f ≤ s.card • n ; nsmul_eq_mul (n a) : n • a = ↑n * a ; Finset.sum_nonneg ; Finset.sum_div\n"
     "Finset.Ico_union_Ico_eq_Ico : a ≤ b → b ≤ c → Ico a b ∪ Ico b c = Ico a c ; Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a b c) ; Finset.sum_Ico_consecutive (f) : m ≤ n → n ≤ k → ∑ i ∈ Ico m n, f i + ∑ i ∈ Ico n k, f i = ∑ i ∈ Ico m k, f i\n"
     "Casts: `push_cast`, `exact_mod_cast`, `Nat.cast_pos.mpr`, `Nat.cast_le.mpr`; positivity closes `0 < (n : ℝ)` from `0 < n` in context. Compare terms one block at a time: bound each summand by the block's first term, then the block sum by card • bound."),
    (re.compile(r"Prime|sqrt|\^ 2 = |= m \^ 2|\* m = "),
     "Nat.prime_dvd_prime_iff_eq (hp hq) : p ∣ q ↔ p = q ; Nat.Prime.eq_one_or_self_of_dvd (hp) (m) : m ∣ p → m = 1 ∨ m = p ; Nat.Prime.two_le ; Nat.Prime.pos ; Nat.Prime.one_lt ; Nat.Prime.eq_two_or_odd (hp) : p = 2 ∨ p % 2 = 1\n"
     "Nat.Prime.dvd_mul (hp) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n ; Nat.sq_sub_sq (a b) : a ^ 2 - b ^ 2 = (a + b) * (a - b) (ℕ subtraction: state b ≤ a first, or work in ℤ with `zify`)\n"
     "A square between consecutive squares: `Nat.pow_lt_pow_left : a < b → n ≠ 0 → a ^ n < b ^ n` and `Nat.pow_lt_pow_iff_left : n ≠ 0 → (a ^ n < b ^ n ↔ a < b)` pin m; Nat.exists_mul_self (x) : (∃ n, n * n = x) ↔ x.sqrt * x.sqrt = x ; Nat.le_sqrt ; Nat.sqrt_lt ; Nat.eq_sqrt\n"
     "For a product of primes equal to a factorisation `(m - p - q) * (m + p + q) = 5 * p * q`, the divisor of the right side is one of 1, 5, p, q, 5p, 5q, pq, 5pq: case on `Nat.Prime.eq_one_or_self_of_dvd` and `Nat.Prime.dvd_mul`, then `omega`/`nlinarith`."),
    (re.compile(r"Coprime|gcd"),
     "Nat.coprime_primes (hp hq) : p.Coprime q ↔ p ≠ q ; Nat.Prime.coprime_iff_not_dvd (hp) : p.Coprime n ↔ ¬p ∣ n ; Nat.Coprime.pow (m n) : k.Coprime l → (k ^ m).Coprime (l ^ n)\n"
     "Nat.Coprime.dvd_of_dvd_mul_left : k.Coprime m → k ∣ m * n → k ∣ n ; Nat.Coprime.gcd_eq_one ; Nat.gcd_comm ; a closed Coprime such as Nat.Coprime 16 125 is `by norm_num`."),
)


def sheet_for(goal_text: str) -> str:
    """The sheets this goal's vocabulary triggers, first 3, at most 16 lines."""

    target = goal_text.split("⊢", 1)[1] if "⊢" in goal_text else goal_text
    hits = [sheet for pattern, sheet in SHEETS if pattern.search(target) or pattern.search(goal_text)]
    return "\n".join("\n".join(hits[:3]).splitlines()[:16])


def notes_for(text: str) -> str:
    """The framework entries this message triggers, and only those."""

    hits = [note for pattern, note in NOTES if pattern.search(text)]
    return "\n".join(f"- {h}" for h in hits[:3])
