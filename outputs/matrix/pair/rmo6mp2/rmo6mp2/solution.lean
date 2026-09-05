import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib

attribute [instance 2000] instPowNat

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b} 10) := by
  refine ⟨?show_10, ?min_10⟩
  case show_10 =>
    have h_witness : 10 ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} := by
      exact ⟨1, 10, by norm_num⟩
    have h_lower : ∀ n, n ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} → 10 ≤ n := by
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : 2 ^ 4 ∣ a ^ 2 * b ^ 5 := by
        have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
        rw [this] at hdiv
        exact Nat.dvd_trans (by simp [Nat.pow_mul, Nat.mul_assoc]) hdiv
      have h5 : 5 ^ 3 ∣ a ^ 2 * b ^ 5 := by
        have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
        rw [this] at hdiv
        exact Nat.dvd_trans (by simp [Nat.pow_mul, Nat.mul_assoc]) hdiv
      have h2_prime : Nat.Prime 2 := by
        trivial
      have h2_dvd_pow : 2 ∣ a ^ 2 * b ^ 5 := by
        omega
      have h2_cases : 2 ∣ a ^ 2 ∨ 2 ∣ b ^ 5 := by
        have h : Nat.Prime 2 := h2_prime
        exact h.dvd_mul.mp h2_dvd_pow
      have h2a_or_h2b : 2 ∣ a ∨ 2 ∣ b := by
        have h2a_or_h2b : 2 ∣ a ∨ 2 ∣ b := by
          have h3 : 2 ∣ a ^ 2 ∨ 2 ∣ b ^ 5 := h2_cases
          cases h3 with
          | inl h3 =>
            have h4 : 2 ∣ a := by
              have h5 : Nat.Prime 2 := h2_prime
              exact Nat.Prime.dvd_of_dvd_pow h5 h3
            exact Or.inl h4
          | inr h3 =>
            have h4 : 2 ∣ b := by
              have h5 : Nat.Prime 2 := h2_prime
              exact Nat.Prime.dvd_of_dvd_pow h5 h3
            exact Or.inr h4

        trivial
      have h2a : 2 ∣ a * b := by
        have h2a : 2 ∣ a * b := by exact?
        trivial
      have h5a : 5 ∣ a * b := by
        have h5_prime : Nat.Prime 5 := by norm_num
        have h5_dvd : 5 ∣ a ^ 2 * b ^ 5 := by
          have : (1 : ℕ) ≤ 3 := by decide
          exact Nat.dvd_of_pow_dvd this h5
        have h5_cases : 5 ∣ a ^ 2 ∨ 5 ∣ b ^ 5 := by
          exact (Nat.Prime.dvd_mul h5_prime).mp h5_dvd
        cases h5_cases with
        | inl h5a =>
          have h5b : 5 ∣ a := by
            have h5_prime : Nat.Prime 5 := h5_prime
            exact Nat.Prime.dvd_of_dvd_pow h5_prime h5a
          exact dvd_mul_of_dvd_left h5b b
        | inr h5b =>
          have h5c : 5 ∣ b := by
            have h5_prime : Nat.Prime 5 := h5_prime
            exact Nat.Prime.dvd_of_dvd_pow h5_prime h5b
          exact dvd_mul_of_dvd_right h5c a
      have h10 : 10 ∣ a * b := by
        omega
      have h_pos : 0 < a * b := by
        positivity
      omega
    exact ⟨h_witness, h_lower⟩
  case min_10 =>
    have h_witness : 10 ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} := by
      exact ⟨1, 10, by norm_num⟩
    have h_lower : ∀ n, n ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} → 10 ≤ n := by
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : 2 ^ 4 ∣ a ^ 3 * b ^ 4 := by
        have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
        rw [this] at hdiv
        exact Nat.dvd_trans (by simp) hdiv
      have h5 : 5 ^ 3 ∣ a ^ 3 * b ^ 4 := by
        have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
        rw [this] at hdiv
        exact Nat.dvd_trans (by simp) hdiv
      have h2_cases : 2 ∣ a ∨ 2 ∣ b := by
        have h2_dvd : 2 ∣ a ^ 3 * b ^ 4 := by
          omega
        have h : Nat.Prime 2 := by trivial
        have h2_cases : 2 ∣ a ^ 3 ∨ 2 ∣ b ^ 4 := h.dvd_mul.mp h2_dvd
        cases h2_cases with
        | inl h2a =>
          have h2b : 2 ∣ a := h.dvd_of_dvd_pow h2a
          exact Or.inl h2b
        | inr h2b =>
          have h2c : 2 ∣ b := h.dvd_of_dvd_pow h2b
          exact Or.inr h2c
      have h5_cases : 5 ∣ a ∨ 5 ∣ b := by
        have h5_dvd : 5 ∣ a ^ 3 * b ^ 4 := by
          omega
        have h : Nat.Prime 5 := by norm_num
        have h5_cases : 5 ∣ a ^ 3 ∨ 5 ∣ b ^ 4 := h.dvd_mul.mp h5_dvd
        cases h5_cases with
        | inl h5a =>
          have h5b : 5 ∣ a := h.dvd_of_dvd_pow h5a
          exact Or.inl h5b
        | inr h5b =>
          have h5c : 5 ∣ b := h.dvd_of_dvd_pow h5b
          exact Or.inr h5c
      have h10 : 10 ∣ a * b := by
        have h2ab : 2 ∣ a * b := by
          cases h2_cases with
          | inl h2a => exact dvd_mul_of_dvd_left h2a b
          | inr h2b => exact dvd_mul_of_dvd_right h2b a
        have h5ab : 5 ∣ a * b := by
          cases h5_cases with
          | inl h5a => exact dvd_mul_of_dvd_left h5a b
          | inr h5b => exact dvd_mul_of_dvd_right h5b a
        have h_coprime : Nat.Coprime 2 5 := by decide
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h_coprime h2ab h5ab
      have h_pos : 0 < a * b := by positivity
      exact Nat.le_of_dvd h_pos h10
    exact ⟨h_witness, h_lower⟩

