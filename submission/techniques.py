"""Proof techniques as Lean tactics: defined once in the solution file's
preamble, callable by either model, checked in the harness image. Each entry
is the Lean source and the one line the models see."""
from __future__ import annotations

# Measured on putnam_2018_a1: every run reached `3a - 2018 ∣ 2018 ^ 2` and then
# tried to decide the divisor set of 4072324 (recursion depth, heartbeats).
DVD_CASES = ("""-- `dvd_cases h : N = p ^ a * q ^ b` turns `h : d ∣ N` into the finitely many
-- values of `d`, one goal each, with `d` replaced by the product.
set_option hygiene false in
macro "dvd_cases" h:ident ":" e:term : tactic => `(tactic| (
  rw [show $e by norm_num] at $h:ident
  obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := Nat.dvd_mul.mp $h
  rw [Nat.dvd_prime_pow (by norm_num)] at h₁ h₂
  obtain ⟨i, hi, rfl⟩ := h₁
  obtain ⟨j, hj, rfl⟩ := h₂
  interval_cases i <;> interval_cases j <;> simp_all <;> omega))""",
             "`dvd_cases h : (N : ℕ) = p ^ a * q ^ b` (h : d ∣ N, p q prime numerals): "
             "one goal per divisor d, closing the numeral ones; never `decide` a divisor set.")

TECHNIQUES: tuple[tuple[str, str], ...] = (DVD_CASES,)

PREAMBLE_MARK = "-- techniques defined for this file"


def preamble() -> str:
    """The Lean block that goes after the imports of every solution file."""
    return PREAMBLE_MARK + "\n\n" + "\n\n".join(src for src, _ in TECHNIQUES) + "\n"


def technique_card() -> str:
    """What the models are told about the tactics this file defines."""
    return "Tactics defined in this file, usable anywhere in it:\n" + "\n".join(
        f"- {note}" for _, note in TECHNIQUES)
