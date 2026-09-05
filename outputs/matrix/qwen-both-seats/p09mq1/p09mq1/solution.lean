import Mathlib

theorem mod7_pow2_cases (n : ℕ) : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases ih with
    | inl h =>
      have : 2 ^ (n + 1) % 7 = 2 := by
        rw [pow_succ]
        simp [h, Nat.mul_mod, Nat.pow_mod]
        <;> norm_num
      exact Or.inr (Or.inl this)
    | inr h =>
      cases h with
      | inl h =>
        have : 2 ^ (n + 1) % 7 = 4 := by
          rw [pow_succ]
          simp [h, Nat.mul_mod, Nat.pow_mod]
          <;> norm_num
        exact Or.inr (Or.inr this)
      | inr h =>
        have : 2 ^ (n + 1) % 7 = 1 := by
          rw [pow_succ]
          simp [h, Nat.mul_mod, Nat.pow_mod]
          <;> norm_num
        exact Or.inl this



/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  case mp =>
    intro h
    have h₁ : 2 ^ n % 7 = 1 := by
      have h₂ : 7 ∣ 2 ^ n - 1 := h
      have h₃ : 2 ^ n ≥ 1 := by
        apply Nat.one_le_pow
        linarith
      have h₄ : (2 ^ n - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h₂
      have h₅ : 2 ^ n % 7 = 1 := by
        have h₆ : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := mod7_pow2_cases n
        rcases h₆ with (h₆ | h₆ | h₆)
        · exact h₆
        · exfalso
          have h₇ : 2 ^ n % 7 = 2 := h₆
          have h₈ : (2 ^ n - 1) % 7 = 1 := by
            have h₉ : 2 ^ n ≥ 1 := by
              apply Nat.one_le_pow
              linarith
            omega
          omega
        · exfalso
          have h₇ : 2 ^ n % 7 = 4 := h₆
          have h₈ : (2 ^ n - 1) % 7 = 3 := by
            have h₉ : 2 ^ n ≥ 1 := by
              apply Nat.one_le_pow
              linarith
            omega
          omega
      exact h₅
    have h₂ : n % 3 = 0 := by
      have h₃ : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 := by
        intro k
        induction' k with k ih
        · norm_num
        · simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, ih]
          <;> norm_num
          <;> omega
      have h₄ : ∀ k : ℕ, 2 ^ (3 * k + 1) % 7 = 2 := by
        intro k
        induction' k with k ih
        · norm_num
        · simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, ih]
          <;> norm_num
          <;> omega
      have h₅ : ∀ k : ℕ, 2 ^ (3 * k + 2) % 7 = 4 := by
        intro k
        induction' k with k ih
        · norm_num
        · simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, ih]
          <;> norm_num
          <;> omega
      have h₆ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h₆ with (h₆ | h₆ | h₆)
      · exact h₆
      · exfalso
        have h₇ : n % 3 = 1 := h₆
        have h₈ : ∃ k, n = 3 * k + 1 := by
          use n / 3
          omega
        rcases h₈ with ⟨k, rfl⟩
        have h₉ : 2 ^ (3 * k + 1) % 7 = 2 := h₄ k
        omega
      · exfalso
        have h₇ : n % 3 = 2 := h₆
        have h₈ : ∃ k, n = 3 * k + 2 := by
          use n / 3
          omega
        rcases h₈ with ⟨k, rfl⟩
        have h₉ : 2 ^ (3 * k + 2) % 7 = 4 := h₅ k
        omega
    omega
  case mpr =>
    intro h
    obtain ⟨k, rfl⟩ := h
    have h₁ : 2 ^ (3 * k) % 7 = 1 := by
      induction' k with k ih
      · norm_num
      · simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, ih]
        <;> norm_num
        <;> omega
    have h₂ : 2 ^ (3 * k) ≥ 1 := by
      apply Nat.one_le_pow
      linarith
    have h₃ : (2 ^ (3 * k) - 1) % 7 = 0 := by
      have h₄ : 2 ^ (3 * k) % 7 = 1 := h₁
      have h₅ : (2 ^ (3 * k) - 1) % 7 = 0 := by
        omega
      exact h₅
    have h₄ : 7 ∣ 2 ^ (3 * k) - 1 := Nat.dvd_of_mod_eq_zero h₃
    exact h₄

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  have h_mod : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := by
    apply mod7_pow2_cases
  omega
