import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib

attribute [instance 2000] instPowNat

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b} 10) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  case refine_1 =>
    exact ⟨1, 10, by norm_num⟩
  case refine_2 =>
    intro n hn
    obtain ⟨a, b, ha, hb, h, rfl⟩ := hn
    have h2 : 2 ^ 4 ∣ a ^ 2 * b ^ 5 := by
      have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
      rw [this] at h
      exact Nat.dvd_trans (by simp [Nat.pow_mul, Nat.mul_assoc]) h
    have h5 : 5 ^ 3 ∣ a ^ 2 * b ^ 5 := by
      have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
      rw [this] at h
      exact Nat.dvd_trans (by simp [Nat.pow_mul, Nat.mul_assoc]) h
    have h2ab : (2 : ℕ) ∣ a * b := by
      have h2a : 2 ∣ a ∨ 2 ∣ b := by
        have : (2 : ℕ) ^ 4 ∣ a ^ 2 * b ^ 5 := h2
        have hp : Nat.Prime 2 := by decide
        have hprime : 2 ∣ a ^ 2 * b ^ 5 := by
          exact dvd_trans (by norm_num [Nat.pow_succ, Nat.mul_assoc]) this
        have hdiv : 2 ∣ a ^ 2 ∨ 2 ∣ b ^ 5 := by
          apply hp.dvd_mul.mp
          exact hprime
        cases' hdiv with h2a h2b
        · have : 2 ∣ a := by
            apply Nat.Prime.dvd_of_dvd_pow hp
            exact h2a
          exact Or.inl this
        · have : 2 ∣ b := by
            apply Nat.Prime.dvd_of_dvd_pow hp
            exact h2b
          exact Or.inr this

      cases' h2a with h2a h2b
      · -- Case: 2 divides a
        have : 2 ∣ a * b := by
          exact dvd_mul_of_dvd_left h2a b
        exact this
      · -- Case: 2 divides b
        have : 2 ∣ a * b := by
          exact dvd_mul_of_dvd_right h2b a
        exact this
    have h5ab : (5 : ℕ) ∣ a * b := by
      have h5ab : (5 : ℕ) ∣ a * b := by
        have hp : Nat.Prime 5 := by decide
        have hprime : 5 ∣ a ^ 2 * b ^ 5 := by
          exact dvd_trans (by norm_num [Nat.pow_succ, Nat.mul_assoc]) h5
        have hdiv : 5 ∣ a ^ 2 ∨ 5 ∣ b ^ 5 := by
          apply hp.dvd_mul.mp
          exact hprime
        cases' hdiv with h5a h5b
        · have : 5 ∣ a := by
            apply Nat.Prime.dvd_of_dvd_pow hp
            exact h5a
          have : 5 ∣ a * b := by
            exact dvd_mul_of_dvd_left this b
          exact this
        · have : 5 ∣ b := by
            apply Nat.Prime.dvd_of_dvd_pow hp
            exact h5b
          have : 5 ∣ a * b := by
            exact dvd_mul_of_dvd_right this a
          exact this

      exact h5ab
    have h10 : (10 : ℕ) ∣ a * b := by
      omega
    have hpos : 0 < a * b := by
      positivity
    omega
  case refine_3 =>
    have h10_mem : 10 ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} := by
      exact ⟨1, 10, by norm_num⟩
    have h10_lower : ∀ n, n ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} → 10 ≤ n := by
      intro n hn
      obtain ⟨a, b, ha, hb, h, rfl⟩ := hn
      have h2 : 2 ^ 4 ∣ a ^ 3 * b ^ 4 := by
        have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
        rw [this] at h
        exact Nat.dvd_trans (by simp [Nat.pow_mul, Nat.mul_assoc]) h
      have h5 : 5 ^ 3 ∣ a ^ 3 * b ^ 4 := by
        have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
        rw [this] at h
        exact Nat.dvd_trans (by simp [Nat.pow_mul, Nat.mul_assoc]) h
      have h2ab : (2 : ℕ) ∣ a * b := by
        have hp : Nat.Prime 2 := by decide
        have hprime : 2 ∣ a ^ 3 * b ^ 4 := by
          exact dvd_trans (by norm_num [Nat.pow_succ, Nat.mul_assoc]) h2
        have hdiv : 2 ∣ a ^ 3 ∨ 2 ∣ b ^ 4 := by
          apply hp.dvd_mul.mp
          exact hprime
        cases' hdiv with h2a h2b
        · have : 2 ∣ a := by
            apply Nat.Prime.dvd_of_dvd_pow hp
            exact h2a
          exact dvd_mul_of_dvd_left this b
        · have : 2 ∣ b := by
            apply Nat.Prime.dvd_of_dvd_pow hp
            exact h2b
          exact dvd_mul_of_dvd_right this a
      have h5ab : (5 : ℕ) ∣ a * b := by
        have hp : Nat.Prime 5 := by decide
        have hprime : 5 ∣ a ^ 3 * b ^ 4 := by
          exact dvd_trans (by norm_num [Nat.pow_succ, Nat.mul_assoc]) h5
        have hdiv : 5 ∣ a ^ 3 ∨ 5 ∣ b ^ 4 := by
          apply hp.dvd_mul.mp
          exact hprime
        cases' hdiv with h5a h5b
        · have : 5 ∣ a := by
            apply Nat.Prime.dvd_of_dvd_pow hp
            exact h5a
          exact dvd_mul_of_dvd_left this b
        · have : 5 ∣ b := by
            apply Nat.Prime.dvd_of_dvd_pow hp
            exact h5b
          exact dvd_mul_of_dvd_right this a
      have h10 : (10 : ℕ) ∣ a * b := by
        omega
      have hpos : 0 < a * b := by
        positivity
      exact Nat.le_of_dvd hpos h10
    exact ⟨h10_mem, h10_lower⟩
