"""What `BoardAgent` inherits. One model call with its pacing and reasoning
settings, the plan and probe asks, and `_finish`, which takes the search back
out of a proved file. No loop lives here; the board's loop is in `run/loop.py`.
"""

from __future__ import annotations

import asyncio
import json
import re
import textwrap
import time
from dataclasses import dataclass, field
from typing import Any, Sequence

from re_harness import LLMCallError, Problem, Services

from submission.techniques import PREAMBLE_END
from submission.config import Config, FEEDBACK_CHARS, Ledger, RETRY_BACKOFF_S
from submission.contract import (declared_names, format_messages, refused_before_generation, strip_fences, suggested_tactics, suggestions)
from submission.framework import (statement_probes, alternatives, declaration_name,
                                  graded_theorems, answer_slots, collapse, first_blocks,
                                  have_spans, classify, cursor_goal, drop_lines, fill_answer,
                                  insert_preamble, is_done, normalise_steps, as_goal,
                                  placeholders, render)

# A step is a few lines; the file it goes into is the context. Wide replies are
# the failure mode here, not narrow ones.
# Measured on p08: gpt-oss-120b spent all 2000 tokens reasoning and returned
# `content: None` with `finish_reason: length`, so the call bought nothing.
STEP_TOKENS = 6000
ANSWER_TOKENS = 4000
# Measured on p09: qwen3.5-flash narrates its reasoning as ordinary content and
# the code block after it is what the token limit cuts. Over three samples each,
# reasoning off halves the reply and every one of them begins with the block.
# gpt-oss-120b answers HTTP 400 rather than turn it off, and that 400 is fatal:
# the ledger marks accounting incomplete and never clears it, so the next call
# aborts the problem. The setting is therefore decided by name, never probed.
REASONING = {"effort": "low"}
# The harness reads a reply for at most 180 s and a ReadTimeout leaves the
# ledger unknown, which scores the problem 0 whatever the file says. Measured
# on p10 (v7.79): a 4000-token step call at 19 tokens/s ran 206 s and zeroed a
# proof that had been accepted 38 s earlier. So a call may ask for no more
# tokens than the slowest recent reply rate produces in LATENCY_BUDGET_S.
LATENCY_BUDGET_S = 120.0
PACE_WINDOW = 6
PACE_MIN_TOKENS = 400
PACE_FLOOR = 1200
NO_REASONING = {"enabled": False}
NARRATES = ("qwen",)
GOAL_CHARS = 4000
FILE_CHARS = 8000
PLAN_TOKENS = 1500

PLANNER_SYSTEM = """You are a competition mathematician. You are given one goal from a
Lean 4 proof, with its hypotheses.

Say how to prove it, in at most six short lines. Name the key fact: the modulus,
the witness, the identity, the bound, the induction, the case split. Give the
value when it is a number. Write mathematics, not Lean, and do not restate the
goal."""
# The finish pass is free of tokens but not of clock, so it is bounded.
MAX_COLLAPSE = 24
# Measured on p08: a file the REPL checks in 570ms timed out at the comparator's
# 180s, because the kernel there re-checks the term and nlinarith's are huge.
MAX_LIGHTEN = 16
# Below this a proof is already small; tidying it only risks it.
TIDY_ABOVE_BYTES = 2000


def below_header(text: str) -> str:
    """The file without the technique block: the tidy threshold is about the
    proof's size, and the block is the same 1.8 KB in every file."""
    i = text.find(PREAMBLE_END)
    return text[i + len(PREAMBLE_END):] if i >= 0 else text
HEAVY = ("nlinarith", "polyrith", "decide", "interval_cases")
LIGHTER = ("linarith", "norm_num", "positivity", "simp", "omega", "ring")
LOOSE_DRAIN_S = 30.0
MAX_DELETIONS = 12
# Each try is one check, and a check is 60ms against a reply's seconds.
MAX_PREFIXES = 8
FINISH_RESERVE_S = 300.0
# Lean's budgets are deterministic, so raising them is sound; it buys that
# determinism with wall clock, which the comparator caps at 180s. Measured on
# p06_pow_mod: what a large power needs is recursion depth, not heartbeats.
RAISED_BUDGETS = ("set_option maxHeartbeats 400000\n"
                     "set_option maxRecDepth 8000\n"
                     "set_option exponentiation.threshold 4000")
# The comparator allows 180 seconds, so a file that only just compiles here is
# not safe there. Recorded, never silently accepted.
SLOW_COMPILE_MS = 150_000

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

# Section 3 of the framework: what Lean's message does not say. Sent only when
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


# Section 4 of the framework: the names the loaded Mathlib has, given before
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


@dataclass
class Feedback:
    """What to tell the next model, and who earned it."""

    author: str
    text: str
    kind: str = "rejected"

    def lead(self, model: str) -> str:
        if self.kind == "probe":
            return "The probe you asked for printed"
        if self.kind == "empty":
            return ("Your last reply contained no Lean. Reply with one ```lean block "
                    "of tactic lines and nothing else. What Lean last said was")
        if self.kind == "cut":
            return ("Your last reply ran out of tokens before its code block ended, so "
                    "none of it could be used. You are writing a whole proof; write the "
                    "next step and stop. What Lean last said was")
        if self.kind == "withdrawn":
            return "A decomposition posted at this goal was taken back"
        if self.kind == "drift":
            return ("These facts compiled but left the goal standing, so they have been "
                    "removed. Reshape the goal or close it directly. They were")
        if self.author == model:
            return "Your last step was rejected and has been removed. Lean said"
        return f"A {self.author} attempt on this goal was rejected. Lean said"


@dataclass
class State:
    """The proof and what the last check said about it."""

    text: str
    goal: str = ""
    line: int = 0
    messages: list[dict[str, Any]] = field(default_factory=list)
    accepted: bool = False
    focus: int = 0
    goals: int = 0


VACUOUS = re.compile(r"^\S[^:]*:\s*(?:True|Type)\s*$", re.M)


def stalled(before: State, after: State) -> bool:
    """A step that grew the file and left the proof state exactly as it was."""

    return (bool(before.goal) and after.goal == before.goal
            and after.text != before.text
            and len(placeholders(after.text)) >= len(placeholders(before.text)))


class FrameworkAgent:
    def __init__(self, config: Config | None = None):
        self.config = config or Config.from_env()
        # Per model: (completion tokens, seconds) of each reply, for _paced.
        self._pace: dict[str, list[tuple[int, float]]] = {}

    def _reasoning(self, model: str) -> dict[str, Any]:
        """Reasoning a model narrates in its content crowds out the step."""

        return NO_REASONING if any(n in model for n in NARRATES) else REASONING

    async def _look(self, text: str, services: Services, focus: int = 0) -> State:
        """One check does both jobs: it adjudicates, and it prints the next goal."""

        open_goals = len(placeholders(text))
        focus = min(max(focus, 0), open_goals - 1) if open_goals else 0
        source, line = render(text, focus)
        check = await services.lean.check_file(source)
        return State(text=text, goal=cursor_goal(check.messages, line), line=line,
                     messages=list(check.messages), accepted=check.accepted,
                     focus=focus, goals=open_goals)

    async def _finish(self, state: State, services: Services, time_left) -> State:
        """Take the search out of a finished file: the comparator allows 180s."""

        state = await self._substitute_search(state, services)
        # Measured on p08: both passes turned a file the comparator accepted
        # into one it timed out on, because deleting a fact a closer was using
        # makes that closer redo the work in a term the kernel then re-checks.
        # A short file has nothing to win here, and §4 says not to touch it.
        if len(below_header(state.text)) > TIDY_ABOVE_BYTES:
            state = await self._lighten(state, services, time_left)
            state = await self._prune(state, services, time_left)
        for _ in range(MAX_COLLAPSE):
            blocks = first_blocks(state.text)
            if not blocks or time_left() < FINISH_RESERVE_S:
                break
            collapsed = None
            for tactic in alternatives(blocks[0].group(2)):
                probe = await self._look(collapse(state.text, blocks[0], tactic), services)
                if probe.accepted:
                    collapsed = probe
                    break
            if collapsed is None:
                break
            state = collapsed
        return state

    async def _lighten(self, state: State, services: Services, time_left) -> State:
        """Make the finished term small.

        Measured on p08: `nlinarith` with three hints checks in 348ms here and
        times out at the comparator's 180s, with one hint it passes."""

        for rewrite in lighter_forms(state.text)[:MAX_LIGHTEN]:
            if time_left() < FINISH_RESERVE_S:
                break
            probe = await self._look(rewrite, services)
            if probe.accepted and is_done(probe.text):
                state = probe
        return state

    async def _prune(self, state: State, services: Services, time_left) -> State:
        """Delete facts the finished proof does not use.

        Only sound now: while a `sorry` remains, no deletion can break anything."""

        tried: set[str] = set()
        for _ in range(MAX_DELETIONS):
            if time_left() < FINISH_RESERVE_S:
                break
            spans = [s for s in have_spans(state.text) if s[2] not in tried]
            if not spans:
                break
            start, end, statement = spans[0]
            tried.add(statement)
            probe = await self._look(
                drop_lines(state.text, range(start, end + 1)), services)
            if probe.accepted and is_done(probe.text):
                state = probe
        return state

    async def _substitute_search(self, state: State, services: Services) -> State:
        """Replace each `exact?` with the term it printed, keeping the search
        call when the term does not re-elaborate."""

        if "exact?" not in state.text and "apply?" not in state.text:
            return state
        for term in suggested_tactics(suggestions(state.messages))[:4]:
            probe = await self._look(state.text.replace("exact?", term, 1), services)
            if probe.accepted:
                return probe
        return state

    async def _probe(self, state: State, block: str, services: Services) -> str:
        """A probe sits above the theorem, is read from its own check, and goes."""

        check = await services.lean.check_file(insert_preamble(state.text, block))
        printed = [str(m.get("data", "")).strip() for m in check.messages
                   if isinstance(m, dict) and m.get("severity") in ("info", "information")]
        return "\n".join(printed)[:FEEDBACK_CHARS] or "nothing"

    async def _ask_plan(self, problem: Problem, state: State, services: Services,
                        ledger: Ledger, model: str = "", avoid: Sequence[str] = ()) -> str:
        """The mathematics, from the model that answers in mathematics. Routes
        already tried on this declaration are named so the next one differs."""

        ask = (f"Problem: {problem.description}\n\nThe goal, as Lean reports it:\n"
               f"{state.goal[:GOAL_CHARS]}\n\nHow do you prove this?")
        sheet = sheet_for(state.goal)
        if sheet:
            # The route hints on the sheets (squeeze between powers, prime
            # dividing a factor, block the sum) are for the planner as much as
            # for the writer; the names tell it what Mathlib can do in one step.
            ask += f"\n\nWhat the loaded Mathlib has for this goal's vocabulary:\n{sheet}"
        if avoid:
            tried = "\n".join(f"- {a[:300]}" for a in list(avoid)[-3:])
            ask += ("\n\nRoutes already tried on this goal that did not work out. "
                    f"Give a different one:\n{tried}")
        # Measured on p10: with reasoning on, the plan came back as "The user is
        # asking me to prove a theorem in Lean 4", which costs a call and enters
        # every later prompt. Reasoning stays on only where it is the answer.
        reply, _ = await self._call(model or self.config.lines[0], ask, PLAN_TOKENS,
                                    services, ledger, PLANNER_SYSTEM)
        return strip_fences(reply).strip()[:GOAL_CHARS]

    async def _share(self, problem: Problem, text: str, services: Services,
                     ledger: Ledger, events: list[dict[str, Any]]) -> str:
        """The fact several theorems need, hoisted above them before any step.
        Both models are asked at once and every distinct statement that
        elaborates is kept: a true lemma costs nothing, and which form the
        proof wants (`%` or `[MOD]`) decided 4 of 6 p09 runs at t=50s."""

        ask = (f"Problem: {problem.description}\n\nFile:\n{text[:FILE_CHARS]}\n\n"
               f"These {graded_theorems(problem.challenge)} theorems are "
               "graded together and share their mathematics. Name the one fact "
               "more than one of them needs, and state it as a standalone Lean 4 "
               "`theorem` above them. Reply with one ```lean block holding that "
               "declaration and nothing else. Leave its body `sorry`; proving it "
               "is a later turn.")
        # Measured on p09 (6 of 6 runs): with reasoning on, qwen answered this
        # with a page of prose and no declaration; only gpt-oss's lemma stayed.
        replies = await asyncio.gather(*(
            self._call(line, ask, STEP_TOKENS, services, ledger,
                       think=not any(n in line for n in NARRATES))
            for line in self.config.lines[:2]))
        for said, _ in replies:
            block = strip_fences(said).strip()
            named = declaration_name(block)
            if not named or named in declared_names(text):
                events.append({"stage": "share", "name": named, "kept": False})
                continue
            candidate = insert_preamble(text, as_goal(block) or block)
            check = await services.lean.check_file(candidate)
            kept = not classify(check.messages)[3]
            events.append({"stage": "share", "name": named, "kept": kept})
            if kept:
                text = candidate
        return text

    async def _resolve_answers(self, problem: Problem, text: str, names: Sequence[str],
                               services: Services, ledger: Ledger,
                               events: list[dict[str, Any]]) -> str:
        """An answer slot is a number to compute, never a number to guess.

        A slot left as `sorry` is unreachable by the cursor and banned by the
        grader, so an unfilled one is reported and asked for again."""

        # A slot left as `sorry` makes the theorem unprovable and the goal
        # display empty, so the loop that follows is worth nothing. Measured on
        # p10: 72 turns asked about a goal Lean could not print. Both models
        # get a turn at it before that happens.
        note = ""
        # A slot the statement equates to a closed term is evaluated here, no
        # model asked (measured on p06: both failed to write the `#eval`).
        own = statement_probes(text, answer_slots(text))
        if own:
            check = await services.lean.check_file(insert_preamble(text, "\n".join(own)))
            values = printed_numbers(check.messages)
            missing = answer_slots(text)
            for name, value in zip(missing, values):
                text = fill_answer(text, name, value)
            events.append({"stage": "probe", "by": "harness", "asked": list(missing),
                           "printed": values[:len(missing)], "unfilled": list(answer_slots(text))})
        for attempt in range(4):
            missing = answer_slots(text)
            if not missing:
                break
            ask = (f"Write one `#eval` line per name, in this order: {', '.join(missing)}.\n"
                   "Each must compute the value, not state it: search a range, or "
                   "evaluate the definition.\n\n"
                   f"Problem: {problem.description}\n\nFile:\n{text[:FILE_CHARS]}\n\n"
                   "Lean 4 with Mathlib. Output the `#eval` lines only. Each must print "
                   "one natural number and nothing else, so the whole search goes in "
                   "the expression: `#eval ((List.range 200).filter (fun n => P n))."
                   "getLast?.getD 0` for a largest, `.head?.getD 0` for a least. A "
                   "line that prints `true` or `some n` is not an answer." + note)
            asking = self.config.lines[attempt % len(self.config.lines)]
            reply, _ = await self._call(
                asking, ask, ANSWER_TOKENS, services, ledger, think=True)
            probes = [l for l in strip_fences(reply).splitlines()
                      if l.strip().startswith("#eval")]
            if not probes:
                note = "\n\nYour last reply contained no `#eval` line."
                continue
            # Measured on p07: three `#eval` lines for one name, the answer and
            # two checks of it. The first printed value fills the slot, and a
            # slot filled wrong is a false theorem no later step can recover.
            if len(probes) != len(missing) and attempt < 2:
                note = (f"\n\nYour last reply had {len(probes)} `#eval` lines for "
                        f"{len(missing)}. Give exactly one per name, in that order, "
                        "and nothing else.")
                continue
            probes = probes[:len(missing)]
            check = await services.lean.check_file(insert_preamble(text, "\n".join(probes)))
            values = printed_numbers(check.messages)
            for name, value in zip(missing, values):
                text = fill_answer(text, name, value)
            left = answer_slots(text)
            events.append({"stage": "probe", "by": asking, "asked": list(missing),
                           "printed": values[:len(missing)], "unfilled": list(left)})
            note = (f"\n\nThese slots are still unfilled: {', '.join(left)}. Each `#eval` "
                    "must print one bare numeral." if left else "")
            if left and check.messages:
                note += "\nLean said:\n" + format_messages(check.messages)[:600]
        return text

    async def _call(self, model: str, prompt: str, max_tokens: int, services: Services,
                    ledger: Ledger, system: str = "", think: bool = False,
                    tools: Sequence[Any] = ()) -> tuple[str, str]:
        """The reply and why the provider stopped, which is not always `stop`.

        Reasoning is off for steps because it crowds the block out of the reply.
        It stays on where thinking is the answer: the plan, and the arithmetic
        behind a numeric slot."""

        max_tokens = self._paced(model, max_tokens)
        for wait in (0.0,) + RETRY_BACKOFF_S:
            if wait:
                await asyncio.sleep(wait)
            started = time.monotonic()
            try:
                reply = await services.llm.complete(
                    model=model,
                    messages=[{"role": "system", "content": system or FRAMEWORK_SYSTEM},
                              {"role": "user", "content": prompt}],
                    max_tokens=max_tokens,
                    temperature=0.4,
                    reasoning=REASONING if think else self._reasoning(model),
                    **({"tools": list(tools),
                        "tool_choice": {"type": "function",
                                        "function": {"name": "answer"}}} if tools else {}),
                )
            except LLMCallError as exc:
                if refused_before_generation(exc):
                    continue
                raise
            ledger.record(reply.usage)
            self._pace.setdefault(model, []).append(
                (int((reply.usage or {}).get("completion_tokens") or 0), time.monotonic() - started))
            said = tool_lines(reply.tool_calls) or spoken(reply.content or "")
            return said, reply.finish_reason or ""
        return "", ""

    def _paced(self, model: str, want: int) -> int:
        """`want` tokens, or what the slowest of the model's recent replies
        would produce inside LATENCY_BUDGET_S, whichever is less."""

        rates = [t / s for t, s in self._pace.get(model, [])[-PACE_WINDOW:]
                 if t >= PACE_MIN_TOKENS and s > 0]
        if len(rates) < 2:
            return want
        return max(PACE_FLOOR, min(want, int(min(rates) * LATENCY_BUDGET_S)))


# Measured on p10: a model that reasons returns its draft inside `<think>`
# tags, and the ten `#eval` lines it tried there are not its answer.
THINKING = re.compile(r"<think>.*?(?:</think>|\Z)", re.S | re.I)


# Measured twice, and the second measurement is the one that counts: asking
# OpenRouter directly, qwen honours a forced tool call and gpt-oss ignores it
# without error, but the same request through the harness answers HTTP 404,
# `no endpoints found that support the provided tool_choice`, which marks the
# budget incomplete and ends the problem. A tool call is read if one arrives
# and never asked for.
def tool_lines(calls: Sequence[Any]) -> str:
    """The strings a tool call carried, if the model made one."""

    for call in calls or ():
        body = (call or {}).get("function", {}).get("arguments")
        try:
            fields = json.loads(body) if isinstance(body, str) else body
        except ValueError:
            continue
        for value in (fields or {}).values():
            if isinstance(value, list) and all(isinstance(v, str) for v in value):
                return "\n".join(value)
    return ""


def spoken(reply: str) -> str:
    """What the model said, without the thinking it said it in."""

    return THINKING.sub("", reply).strip()


BUDGET_RETRY = "__budget__"


def is_probe(block: str) -> bool:
    """A reply that only computes something is a probe, not a step."""

    lines = [l for l in block.splitlines() if l.strip()]
    return bool(lines) and all(l.strip().startswith(("#eval", "#check", "#print"))
                               for l in lines)
# A step is tactic text, except a whole auxiliary declaration, which §4 allows
# and which is the only way to state a fact two theorems share.
STEP_BAN = re.compile(r"^\s*(import|example|axiom)\b|```|native_decide|admit", re.M)


# Measured: `#eval (List.range 100).find? p` prints `some 19`, which is the
# right answer computed the right way and was being discarded as not a numeral.
PRINTED = re.compile(r"\A(?:Option\.)?some\s+(-?\d+)\Z|\A(-?\d+)\Z")


def printed_numbers(messages: Sequence[Any]) -> list[str]:
    """What `#eval` printed, in order, as numbers."""

    out = []
    for m in messages:
        if isinstance(m, dict) and m.get("severity") in ("info", "information"):
            found = PRINTED.match(str(m.get("data", "")).strip())
            if found:
                out.append(found.group(1) or found.group(2))
    return out


FENCED = re.compile(r"```(?:lean4?)?\s*\n(.*?)```", re.DOTALL | re.IGNORECASE)


# What a Lean tactic line can start with. Measured on p08: qwen answers in
# prose as often as in Lean, and prose spliced into the file is a wasted check.
OPENERS = (
    "have", "let", "set", "show", "intro", "intros", "induction", "cases",
    "rcases", "obtain", "refine", "exact", "apply", "constructor", "use",
    "rfl", "simp", "simp_all", "simp_only", "norm_num", "norm_cast", "push_cast",
    "omega", "decide", "linarith", "nlinarith", "positivity", "polyrith", "ring",
    "ring_nf", "field_simp", "gcongr", "bound", "aesop", "tauto", "trivial",
    "interval_cases", "by_contra", "push_neg", "rw", "rwa", "subst", "subst_vars",
    "unfold", "calc", "left", "right", "exfalso", "contradiction", "specialize",
    "all_goals", "any_goals", "first", "repeat", "conv", "zify", "rify", "qify",
    "nth_rewrite", "change", "convert", "ext", "funext", "split", "split_ifs",
    "theorem", "lemma", "private", "set_option", "#eval", "#check", "#print",
    "·", "|", "<;>", "sorry", "skip", "-",
)


def lean_lines(text: str) -> str:
    """The longest run of lines that could be Lean, prose dropped."""

    runs, current = [], []
    for line in text.split("\n"):
        body = line.strip()
        opens = body.startswith(OPENERS) or (line.startswith((" ", "\t")) and bool(current))
        if body and opens:
            current.append(line)
        elif not body and current:
            current.append(line)
        else:
            runs.append(current)
            current = []
    runs.append(current)
    best = max(runs, key=lambda r: len([l for l in r if l.strip()]), default=[])
    return textwrap.dedent("\n".join(best)).strip()


def screen_step(reply: str, allow_sorry: bool = False) -> str:
    """A step is tactic lines. Prose around them is dropped, not spliced.
    On the board a `sorry` is a subgoal being posted, so the board allows it."""

    blocks = [b for b in FENCED.findall(reply) if b.strip()]
    raw = strip_fences(blocks[-1] if blocks else reply)
    block = normalise_steps(lean_lines(raw) if not blocks else raw)
    # A lone `by` on the first line is the model framing its block, not a step.
    # Measured on p09: `strip()` dedented only the first line after it, and 13
    # of one model's 34 replies reached Lean as `unexpected token 'have'`.
    lines = block.split("\n")
    if lines and lines[0].strip() == "by":
        lines = lines[1:]
    block = textwrap.dedent("\n".join(lines)).strip()
    if not block or STEP_BAN.search(block):
        return ""
    # A `sorry` is a placeholder for a goal that gets its own turn: a branch of
    # an `induction ... with`, or the body of a lemma being introduced. Anywhere
    # else it is the model closing the goal it was asked to prove.
    if (re.search(r"\bsorry\b", block) and not allow_sorry and "with" not in block
            and "|" not in block and not declaration_name(block)):
        return ""
    # A step that does nothing still enters the file and every later prompt.
    if all(l.strip() in ("", "skip") for l in block.splitlines()):
        return ""
    return block


HINTED = re.compile(r"\b(nlinarith|linarith|positivity|norm_num)\s*\[([^\]]*)\]")


def lighter_forms(text: str) -> list[str]:
    """Cheaper spellings of the same file, cheapest first.

    A hint list is what makes a certificate large, so it is trimmed before the
    tactic itself is traded down."""

    out: list[str] = []
    for m in HINTED.finditer(text):
        hints = [h.strip() for h in m.group(2).split(",") if h.strip()]
        if len(hints) > 1:
            for hint in hints:
                out.append(text[:m.start()] + f"{m.group(1)} [{hint}]" + text[m.end():])
        if hints:
            out.append(text[:m.start()] + m.group(1) + text[m.end():])
    for heavy in HEAVY:
        start = 0
        while (at := text.find(heavy, start)) != -1:
            for light in LIGHTER:
                out.append(text[:at] + light + text[at + len(heavy):])
            start = at + len(heavy)
    return out
