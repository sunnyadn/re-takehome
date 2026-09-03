import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib

attribute [instance 2000] instPowNat

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b} 10) := by
  refine ⟨?_, ?_⟩
  case refine_1 =>
    have hmem : (10 : ℕ) ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} := by
      exact ⟨1, 10, by norm_num⟩
    have hlower : ∀ n, n ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} → 10 ≤ n := by
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : 2 ∣ a ^ 2 * b ^ 5 := by
        have : 2 ∣ 2000 := by norm_num
        exact dvd_trans this hdiv
      have h5 : 5 ∣ a ^ 2 * b ^ 5 := by
        have : 5 ∣ 2000 := by norm_num
        exact dvd_trans this hdiv
      -- obtain divisibility by 2 and 5 of `a * b`
      have h2ab : (2 : ℕ) ∣ a * b := by
        rcases (Nat.prime_two).dvd_mul.1 h2 with h2a | h2b
        ·
          have : (2 : ℕ) ∣ a := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two) h2a
          exact this.trans (Nat.dvd_mul_right _ _)
        ·
          have : (2 : ℕ) ∣ b := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two) h2b
          exact this.trans (Nat.dvd_mul_left _ _)
      have h5ab : (5 : ℕ) ∣ a * b := by
        rcases (Nat.prime_five).dvd_mul.1 h5 with h5a | h5b
        ·
          have : (5 : ℕ) ∣ a := (Nat.Prime.dvd_of_dvd_pow Nat.prime_five) h5a
          exact this.trans (Nat.dvd_mul_right _ _)
        ·
          have : (5 : ℕ) ∣ b := (Nat.Prime.dvd_of_dvd_pow Nat.prime_five) h5b
          exact this.trans (Nat.dvd_mul_left _ _)
      have h2ab' : 2 ∣ a * b := h2ab
      have h5ab' : 5 ∣ a * b := h5ab
      have h10ab : 10 ∣ a * b := by
        have : (2 : ℕ).Coprime 5 := by decide
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd this h2ab' h5ab'
      have hpos : 0 < a * b := mul_pos ha hb
      exact Nat.le_of_dvd hpos h10ab
    exact ⟨hmem, hlower⟩
  case refine_2 =>
    have hmem2 : (10 : ℕ) ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} := by
      exact ⟨1, 10, by norm_num⟩
    have hlower2 : ∀ n, n ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} → 10 ≤ n := by
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : 2 ∣ a ^ 3 * b ^ 4 := by
        have : 2 ∣ 2000 := by norm_num
        exact dvd_trans this hdiv
      have h5 : 5 ∣ a ^ 3 * b ^ 4 := by
        have : 5 ∣ 2000 := by norm_num
        exact dvd_trans this hdiv
      have h2ab : (2 : ℕ) ∣ a * b := by
        rcases (Nat.prime_two).dvd_mul.1 h2 with h2a | h2b
        ·
          have : (2 : ℕ) ∣ a := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two) h2a
          exact this.trans (Nat.dvd_mul_right _ _)
        ·
          have : (2 : ℕ) ∣ b := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two) h2b
          exact this.trans (Nat.dvd_mul_left _ _)
      have h5ab : (5 : ℕ) ∣ a * b := by
        rcases (Nat.prime_five).dvd_mul.1 h5 with h5a | h5b
        ·
          have : (5 : ℕ) ∣ a := (Nat.Prime.dvd_of_dvd_pow Nat.prime_five) h5a
          exact this.trans (Nat.dvd_mul_right _ _)
        ·
          have : (5 : ℕ) ∣ b := (Nat.Prime.dvd_of_dvd_pow Nat.prime_five) h5b
          exact this.trans (Nat.dvd_mul_left _ _)
      have h10ab : 10 ∣ a * b := by
        have : (2 : ℕ).Coprime 5 := by ring
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd this h2ab h5ab
      have hpos : 0 < a * b := mul_pos ha hb
      exact Nat.le_of_dvd hpos h10ab
    exact ⟨hmem2, hlower2⟩
