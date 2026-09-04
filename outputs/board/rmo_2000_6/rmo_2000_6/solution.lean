import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib

attribute [instance 2000] instPowNat

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b} 10) := by
  refine ⟨?_, ?_⟩
  case refine_1 =>
    refine ⟨?_, ?_⟩
    have h_exists : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ 10 = a * b := by
      exact ⟨1, 10, by norm_num⟩
    exact h_exists
    intro n hn
    obtain ⟨a, b, ha, hb, h, rfl⟩ := hn
    have h2000 : 2000 = 2 ^ 4 * 5 ^ 3 := by norm_num
    have h2a : 2 ∣ a ∨ 2 ∣ b := by
      have h2p : Nat.Prime 2 := by decide
      have h2dvd : 2 ∣ a ^ 2 * b ^ 5 := dvd_trans (by decide) h
      have h2a' : 2 ∣ a ^ 2 ∨ 2 ∣ b ^ 5 := by
        apply (Nat.Prime.dvd_mul h2p).mp
        exact h2dvd
      cases h2a' with
      | inl h2a'' =>
        have h2a''' : 2 ∣ a := by
          apply Nat.Prime.dvd_of_dvd_pow h2p
          exact h2a''
        exact Or.inl h2a'''
      | inr h2b'' =>
        have h2b''' : 2 ∣ b := by
          apply Nat.Prime.dvd_of_dvd_pow h2p
          exact h2b''
        exact Or.inr h2b'''
    have h5a : 5 ∣ a ∨ 5 ∣ b := by
      have h5p : Nat.Prime 5 := by decide
      have h5dvd : 5 ∣ a ^ 2 * b ^ 5 := dvd_trans (by decide) h
      have h5a' : 5 ∣ a ^ 2 ∨ 5 ∣ b ^ 5 := by
        apply (Nat.Prime.dvd_mul h5p).mp
        exact h5dvd
      cases h5a' with
      | inl h5a'' =>
        have h5a''' : 5 ∣ a := by
          apply Nat.Prime.dvd_of_dvd_pow h5p
          exact h5a''
        exact Or.inl h5a'''
      | inr h5b'' =>
        have h5b''' : 5 ∣ b := by
          apply Nat.Prime.dvd_of_dvd_pow h5p
          exact h5b''
        exact Or.inr h5b'''
    have h10 : 10 ∣ a * b := by
      have h2ab : 2 ∣ a * b := by
        cases h2a with
        | inl h2a =>
          exact dvd_mul_of_dvd_left h2a b
        | inr h2b =>
          exact dvd_mul_of_dvd_right h2b a
      have h5ab : 5 ∣ a * b := by
        cases h5a with
        | inl h5a =>
          exact dvd_mul_of_dvd_left h5a b
        | inr h5b =>
          exact dvd_mul_of_dvd_right h5b a
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h2ab h5ab
    have h_final : 10 ≤ a * b := by
      have h_pos : 0 < a * b := mul_pos ha hb
      exact Nat.le_of_dvd h_pos h10
    trivial
  case refine_2 =>
    refine ⟨?_, ?_⟩
    have : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ 10 = a * b := by
      refine ⟨5, 2, by decide, by decide, ?_, rfl⟩
      norm_num
    exact this
    intro n hn
    obtain ⟨a, b, ha, hb, h, rfl⟩ := hn
    have : 2000 ∣ a ^ 3 * b ^ 4 := h
    have h2 : 2 ∣ a ^ 3 * b ^ 4 := by
      exact dvd_trans (by decide) this
    have h5 : 5 ∣ a ^ 3 * b ^ 4 := by
      exact dvd_trans (by decide) this
    have h2a : 2 ∣ a ∨ 2 ∣ b := by
      have h2p : Nat.Prime 2 := by decide
      have h2dvd : 2 ∣ a ^ 3 * b ^ 4 := h2
      have h2a' : 2 ∣ a ^ 3 ∨ 2 ∣ b ^ 4 := by
        apply (Nat.Prime.dvd_mul h2p).mp
        exact h2dvd
      cases h2a' with
      | inl h2a'' =>
        have h2a''' : 2 ∣ a := by
          apply Nat.Prime.dvd_of_dvd_pow h2p
          exact h2a''
        exact Or.inl h2a'''
      | inr h2b'' =>
        have h2b''' : 2 ∣ b := by
          apply Nat.Prime.dvd_of_dvd_pow h2p
          exact h2b''
        exact Or.inr h2b'''
    have h5a : 5 ∣ a ∨ 5 ∣ b := by
      have h5a : 5 ∣ a ∨ 5 ∣ b := by
        have h5p : Nat.Prime 5 := by decide
        have h5dvd : 5 ∣ a ^ 3 * b ^ 4 := h5
        have h5a' : 5 ∣ a ^ 3 ∨ 5 ∣ b ^ 4 := by
          apply (Nat.Prime.dvd_mul h5p).mp
          exact h5dvd
        cases h5a' with
        | inl h5a'' =>
          have h5a''' : 5 ∣ a := by
            apply Nat.Prime.dvd_of_dvd_pow h5p
            exact h5a''
          exact Or.inl h5a'''
        | inr h5b'' =>
          have h5b''' : 5 ∣ b := by
            apply Nat.Prime.dvd_of_dvd_pow h5p
            exact h5b''
          exact Or.inr h5b'''
      exact h5a
    have h2b : 2 ∣ a * b := by
      cases h2a with
      | inl h2a =>
        have : 2 ∣ a := h2a
        have : 2 ∣ a * b := dvd_mul_of_dvd_left this b
        exact this
      | inr h2b =>
        have : 2 ∣ b := h2b
        have : 2 ∣ a * b := dvd_mul_of_dvd_right this a
        exact this
    have h5b : 5 ∣ a * b := by
      cases h5a with
      | inl h5a =>
        have : 5 ∣ a := h5a
        have : 5 ∣ a * b := dvd_mul_of_dvd_left this b
        exact this
      | inr h5b =>
        have : 5 ∣ b := h5b
        have : 5 ∣ a * b := dvd_mul_of_dvd_right this a
        exact this
    have h10 : 10 ∣ a * b := by
      omega
    have h_final : 10 ≤ a * b := by
      have h_pos : 0 < a * b := mul_pos ha hb
      exact Nat.le_of_dvd h_pos h10
    trivial
