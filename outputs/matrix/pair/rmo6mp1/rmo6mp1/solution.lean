import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib

attribute [instance 2000] instPowNat

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b} 10) := by
  refine ⟨?_, ?_⟩
  refine ⟨?_, ?_⟩
  case refine_1.refine_1 =>
    exact ⟨1, 10, by norm_num⟩
  case refine_1.refine_2 =>
    intro n hn
    obtain ⟨a, b, ha, hb, h, rfl⟩ := hn
    have h2 : 2 ^ 4 ∣ a ^ 2 * b ^ 5 := by
      have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
      rw [this] at h
      exact Nat.dvd_trans (by simp [Nat.mul_dvd_mul_left]) h
    have h5 : 5 ^ 3 ∣ a ^ 2 * b ^ 5 := by
      have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
      rw [this] at h
      exact Nat.dvd_trans (by simp [Nat.mul_dvd_mul_right]) h
    have h2' : (2 : ℕ) ∣ a ^ 2 * b ^ 5 := by
      exact Nat.dvd_of_pow_dvd (by decide) h2
    have h2a : (2 : ℕ) ∣ a ^ 2 ∨ (2 : ℕ) ∣ b ^ 5 :=
      (Nat.prime_two).dvd_mul.mp h2'
    have h2ab : (2 : ℕ) ∣ a ∨ (2 : ℕ) ∣ b := by
      rcases h2a with h2a | h2b
      · left; exact (Nat.prime_two).dvd_of_dvd_pow h2a
      · right; exact (Nat.prime_two).dvd_of_dvd_pow h2b
    have h5' : (5 : ℕ) ∣ a ^ 2 * b ^ 5 := by
      exact Nat.dvd_of_pow_dvd (by decide) h5
    have h5a : (5 : ℕ) ∣ a ^ 2 ∨ (5 : ℕ) ∣ b ^ 5 :=
      (Nat.prime_five).dvd_mul.mp h5'
    have h5ab : (5 : ℕ) ∣ a ∨ (5 : ℕ) ∣ b := by
      rcases h5a with h5a | h5b
      · left; exact (Nat.prime_five).dvd_of_dvd_pow h5a
      · right; exact (Nat.prime_five).dvd_of_dvd_pow h5b
    have h2ab' : (2 : ℕ) ∣ a * b := by
      rcases h2ab with h2a | h2b
      · exact dvd_mul_of_dvd_left h2a _
      · exact dvd_mul_of_dvd_right h2b _
    have h5ab' : (5 : ℕ) ∣ a * b := by
      rcases h5ab with h5a | h5b
      · exact dvd_mul_of_dvd_left h5a _
      · exact dvd_mul_of_dvd_right h5b _
    have h10 : (10 : ℕ) ∣ a * b := by
      have hcop : Nat.Coprime (2 : ℕ) (5 : ℕ) := by decide
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2ab' h5ab'
    have hpos : 0 < a * b := mul_pos ha hb
    exact Nat.le_of_dvd hpos h10
  case refine_2 =>
    refine ⟨?_, ?_⟩
    · exact ⟨5, 2, by norm_num, by norm_num, by norm_num, rfl⟩
    · intro n hn
      obtain ⟨a, b, ha, hb, hdiv, rfl⟩ := hn
      have h2 : (2 : ℕ) ^ 4 ∣ a ^ 3 * b ^ 4 := by
        have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
        rw [this] at hdiv
        exact Nat.dvd_trans (by simp [Nat.mul_dvd_mul_left]) hdiv
      have h5 : (5 : ℕ) ^ 3 ∣ a ^ 3 * b ^ 4 := by
        have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
        rw [this] at hdiv
        exact Nat.dvd_trans (by simp [Nat.mul_dvd_mul_right]) hdiv
      have h2' : (2 : ℕ) ∣ a ^ 3 * b ^ 4 := by
        exact Nat.dvd_of_pow_dvd (by decide) h2
      have h2a : (2 : ℕ) ∣ a ^ 3 ∨ (2 : ℕ) ∣ b ^ 4 :=
        (Nat.prime_two).dvd_mul.mp h2'
      have h2ab : (2 : ℕ) ∣ a ∨ (2 : ℕ) ∣ b := by
        rcases h2a with h2a | h2b
        · left; exact (Nat.prime_two).dvd_of_dvd_pow h2a
        · right; exact (Nat.prime_two).dvd_of_dvd_pow h2b
      have h5' : (5 : ℕ) ∣ a ^ 3 * b ^ 4 := by
        exact Nat.dvd_of_pow_dvd (by decide) h5
      have h5a : (5 : ℕ) ∣ a ^ 3 ∨ (5 : ℕ) ∣ b ^ 4 :=
        (Nat.prime_five).dvd_mul.mp h5'
      have h5ab : (5 : ℕ) ∣ a ∨ (5 : ℕ) ∣ b := by
        rcases h5a with h5a | h5b
        · left; exact (Nat.prime_five).dvd_of_dvd_pow h5a
        · right; exact (Nat.prime_five).dvd_of_dvd_pow h5b
      have h2ab' : (2 : ℕ) ∣ a * b := by
        rcases h2ab with h2a | h2b
        · exact dvd_mul_of_dvd_left h2a _
        · exact dvd_mul_of_dvd_right h2b _
      have h5ab' : (5 : ℕ) ∣ a * b := by
        rcases h5ab with h5a | h5b
        · exact dvd_mul_of_dvd_left h5a _
        · exact dvd_mul_of_dvd_right h5b _
      have h10 : (10 : ℕ) ∣ a * b := by
        have hcop : Nat.Coprime (2 : ℕ) (5 : ℕ) := by decide
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2ab' h5ab'
      have hpos : 0 < a * b := mul_pos ha hb
      exact Nat.le_of_dvd hpos h10
