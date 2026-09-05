import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib

attribute [instance 2000] instPowNat

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b} 10) := by
  refine ⟨?_, ?_⟩
  case refine_1 =>
    have h₁ : 10 ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} := by
      exact ⟨1, 10, by norm_num, by norm_num⟩
    have h₂ : ∀ n, n ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} → 10 ≤ n := by
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : 2 ∣ a ^ 2 * b ^ 5 := by
        have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
        rw [this] at hdiv
        exact Nat.dvd_trans (by simp [Nat.pow_succ, Nat.mul_assoc]) hdiv
      have h5 : 5 ∣ a ^ 2 * b ^ 5 := by
        have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
        rw [this] at hdiv
        exact Nat.dvd_trans (by simp [Nat.pow_succ, Nat.mul_assoc]) hdiv
      have h2a : 2 ∣ a * b := by
        have h2a : 2 ∣ a * b := by
          have h2p : Nat.Prime 2 := by decide
          have h2dvd : 2 ∣ a ^ 2 * b ^ 5 := h2
          have h2a_or_b : 2 ∣ a ^ 2 ∨ 2 ∣ b ^ 5 := by
            apply h2p.dvd_mul.mp
            exact h2dvd
          cases h2a_or_b with
          | inl h2_sq =>
            have h2_a : 2 ∣ a := by
              have h2p' : Nat.Prime 2 := by decide
              exact h2p'.dvd_of_dvd_pow h2_sq
            exact dvd_mul_of_dvd_left h2_a b
          | inr h2_b =>
            have h2_b_div : 2 ∣ b := by
              have h2p' : Nat.Prime 2 := by decide
              exact h2p'.dvd_of_dvd_pow h2_b
            exact dvd_mul_of_dvd_right h2_b_div a
        trivial
      have h5a : 5 ∣ a * b := by
        have h5p : Nat.Prime 5 := by decide
        have h5dvd : 5 ∣ a ^ 2 * b ^ 5 := h5
        have h5a_or_b : 5 ∣ a ^ 2 ∨ 5 ∣ b ^ 5 := by
          apply h5p.dvd_mul.mp
          exact h5dvd
        cases h5a_or_b with
        | inl h5_sq =>
          have h5_a : 5 ∣ a := by
            have h5p' : Nat.Prime 5 := by decide
            exact h5p'.dvd_of_dvd_pow h5_sq
          exact dvd_mul_of_dvd_left h5_a b
        | inr h5_b =>
          have h5_b_div : 5 ∣ b := by
            have h5p' : Nat.Prime 5 := by decide
            exact h5p'.dvd_of_dvd_pow h5_b
          exact dvd_mul_of_dvd_right h5_b_div a
      have h10 : 10 ∣ a * b := by
        omega
      have h15 : 0 < a * b := by
        positivity
      have h16 : 10 ≤ a * b := by
        omega
      trivial
    trivial
  case refine_2 =>
    refine ⟨?_, ?_⟩
    have h₁ : 10 ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} := by
      exact ⟨1, 10, by norm_num, by norm_num, by norm_num, rfl⟩
    have h₂ : ∀ n, n ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} → 10 ≤ n := by
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : 2 ∣ a ^ 3 * b ^ 4 := by
        have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
        rw [this] at hdiv
        exact Nat.dvd_trans (by simp [Nat.pow_succ, Nat.mul_assoc]) hdiv
      have h5 : 5 ∣ a ^ 3 * b ^ 4 := by
        have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
        rw [this] at hdiv
        exact Nat.dvd_trans (by simp [Nat.pow_succ, Nat.mul_assoc]) hdiv
      have h2a : 2 ∣ a * b := by
        have h2p : Nat.Prime 2 := by decide
        have h2dvd : 2 ∣ a ^ 3 * b ^ 4 := h2
        have h2a_or_b : 2 ∣ a ^ 3 ∨ 2 ∣ b ^ 4 := by
          apply h2p.dvd_mul.mp
          exact h2dvd
        cases h2a_or_b with
        | inl h2_sq =>
          have h2_a : 2 ∣ a := by
            have h2p' : Nat.Prime 2 := by decide
            exact h2p'.dvd_of_dvd_pow h2_sq
          exact dvd_mul_of_dvd_left h2_a b
        | inr h2_b =>
          have h2_b_div : 2 ∣ b := by
            have h2p' : Nat.Prime 2 := by decide
            exact h2p'.dvd_of_dvd_pow h2_b
          exact dvd_mul_of_dvd_right h2_b_div a
      have h5a : 5 ∣ a * b := by
        have h5p : Nat.Prime 5 := by decide
        have h5dvd : 5 ∣ a ^ 3 * b ^ 4 := h5
        have h5a_or_b : 5 ∣ a ^ 3 ∨ 5 ∣ b ^ 4 := by
          apply h5p.dvd_mul.mp
          exact h5dvd
        cases h5a_or_b with
        | inl h5_sq =>
          have h5_a : 5 ∣ a := by
            have h5p' : Nat.Prime 5 := by decide
            exact h5p'.dvd_of_dvd_pow h5_sq
          exact dvd_mul_of_dvd_left h5_a b
        | inr h5_b =>
          have h5_b_div : 5 ∣ b := by
            have h5p' : Nat.Prime 5 := by decide
            exact h5p'.dvd_of_dvd_pow h5_b
          exact dvd_mul_of_dvd_right h5_b_div a
      have h10 : 10 ∣ a * b := by
        omega
      have h15 : 0 < a * b := by
        positivity
      have h16 : 10 ≤ a * b := by
        omega
      trivial
    trivial
    intro n hn
    rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
    have h2 : 2 ∣ a ^ 3 * b ^ 4 := by
      have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
      rw [this] at hdiv
      exact Nat.dvd_trans (by simp [Nat.pow_succ, Nat.mul_assoc]) hdiv
    have h5 : 5 ∣ a ^ 3 * b ^ 4 := by
      have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
      rw [this] at hdiv
      exact Nat.dvd_trans (by simp [Nat.pow_succ, Nat.mul_assoc]) hdiv
    have h2a : 2 ∣ a * b := by
      have h2p : Nat.Prime 2 := by decide
      have h2dvd : 2 ∣ a ^ 3 * b ^ 4 := h2
      have h2a_or_b : 2 ∣ a ^ 3 ∨ 2 ∣ b ^ 4 := by
        apply h2p.dvd_mul.mp
        exact h2dvd
      cases h2a_or_b with
      | inl h2_sq =>
        have h2_a : 2 ∣ a := by
          have h2p' : Nat.Prime 2 := by decide
          exact h2p'.dvd_of_dvd_pow h2_sq
        exact dvd_mul_of_dvd_left h2_a b
      | inr h2_b =>
        have h2_b_div : 2 ∣ b := by
          have h2p' : Nat.Prime 2 := by decide
          exact h2p'.dvd_of_dvd_pow h2_b
        exact dvd_mul_of_dvd_right h2_b_div a
    have h5a : 5 ∣ a * b := by
      have h5p : Nat.Prime 5 := by decide
      have h5dvd : 5 ∣ a ^ 3 * b ^ 4 := h5
      have h5a_or_b : 5 ∣ a ^ 3 ∨ 5 ∣ b ^ 4 := by
        apply h5p.dvd_mul.mp
        exact h5dvd
      cases h5a_or_b with
      | inl h5_sq =>
        have h5_a : 5 ∣ a := by
          have h5p' : Nat.Prime 5 := by decide
          exact h5p'.dvd_of_dvd_pow h5_sq
        exact dvd_mul_of_dvd_left h5_a b
      | inr h5_b =>
        have h5_b_div : 5 ∣ b := by
          have h5p' : Nat.Prime 5 := by decide
          exact h5p'.dvd_of_dvd_pow h5_b
        exact dvd_mul_of_dvd_right h5_b_div a
    have h10 : 10 ∣ a * b := by
      omega
    have h16 : 10 ≤ a * b := by
      have hpos : 0 < a * b := by positivity
      exact Nat.le_of_dvd hpos h10
    trivial
