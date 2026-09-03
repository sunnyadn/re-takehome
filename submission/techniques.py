"""Proof techniques as Lean tactics: defined once in the solution file's
preamble, callable by either model, checked in the harness image. Each entry
is the Lean source and the one line the models see."""
from __future__ import annotations

# Measured on putnam_2018_a1 (d ∣ 2² · 1009²) and rmo_2001_2 (d ∣ 5 · p · q, p q
# prime): both boards reached the divisor enumeration and neither model finished it.
DIVISOR_CASES = ("""-- `divisor_cases h : e` (h : d ∣ e) or `divisor_cases h : N = e` (h : d ∣ N,
-- N a numeral) puts one goal per divisor of e, d replaced by it. e is a product
-- of prime variables (Nat.Prime in context), numeral primes and prime powers.
syntax "divisor_split" ident " : " term : tactic
set_option linter.unusedVariables false in
macro_rules
  | `(tactic| divisor_split $h : $a * $b) => `(tactic| (
      obtain ⟨d₁, d₂, h₁, h₂, hd⟩ := Nat.dvd_mul.mp $h
      first | subst hd | rw [← hd] at *
      (divisor_split h₂ : $b) <;> (divisor_split h₁ : $a)))
  | `(tactic| divisor_split $h : $a ^ $k) => `(tactic| (
      rw [Nat.dvd_prime_pow (by norm_num)] at $h:ident
      obtain ⟨i, hi, hd⟩ := $h
      subst hd
      interval_cases i))
  | `(tactic| divisor_split $h : $a) => `(tactic| (
      have hp : Nat.Prime $a := by first | assumption | norm_num
      rcases (Nat.dvd_prime hp).mp $h with hd | hd <;> subst hd))

syntax "divisor_cases" ident " : " term : tactic
macro_rules
  | `(tactic| divisor_cases $h : $l = $r) => `(tactic| (
      rw [show $l = $r by norm_num] at $h:ident
      divisor_split $h : $r))
  | `(tactic| divisor_cases $h : $e) => `(tactic| divisor_split $h : $e)""",
                 "`divisor_cases h : e` (h : d ∣ e, e a product of prime variables with Nat.Prime "
                 "in context, numeral primes and prime powers, such as `5 * p * q` or `2 ^ 2 * 1009 ^ 2`) "
                 "or `divisor_cases h : N = e` for a numeral N: one goal per divisor, d replaced by it; "
                 "for `h : a * b = e` first `have hd : a ∣ e := Dvd.intro _ h`. Never `decide` a divisor set.")

TECHNIQUES: tuple[tuple[str, str], ...] = (DIVISOR_CASES,)

PREAMBLE_MARK = "-- techniques defined for this file"
PREAMBLE_END = "-- end of techniques"


def preamble() -> str:
    """The Lean block that goes after the imports of every solution file."""
    return PREAMBLE_MARK + "\n\n" + "\n\n".join(src for src, _ in TECHNIQUES) + "\n" + PREAMBLE_END + "\n"


def technique_card() -> str:
    """What the models are told about the tactics this file defines."""
    return "Tactics defined in this file, usable anywhere in it:\n" + "\n".join(
        f"- {note}" for _, note in TECHNIQUES)
