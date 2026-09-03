import Mathlib
theorem two_pow_mod_seven (n : ℕ) : 2 ^ n % 7 = 2 ^ (n % 3) % 7 := by
  have h_mod_3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h_mod_3 with (h | h | h) <;> simp [h, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
  case inl =>
    have h2 : 2 % 7 = 2 := by norm_num
    have h3 : 2 ^ n % 7 = 1 := by
      rw [← Nat.mod_add_div n 3]
      simp [h, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod, h2]
      <;> norm_num
      <;> omega
    exact h3
  case inr.inl =>
    have h2 : 2 ^ n % 7 = 2 := by
      rw [← Nat.mod_add_div n 3]
      simp [h, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
      <;> norm_num
      <;> omega
    exact h2
  case inr.inr =>
    have h2 : (2 % 7) ^ n % 7 = 4 := by
      rw [← Nat.mod_add_div n 3]
      simp [h, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
      <;> norm_num
      <;> omega
    exact h2

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have h_mod : (2 ^ n - 1) % 7 = 0 ↔ 2 ^ n % 7 = 1 := by
    have h₁ : 2 ^ n % 7 < 7 := Nat.mod_lt _ (by norm_num)
    have h₂ : 2 ^ n ≥ 1 := Nat.one_le_pow _ _ (by linarith)
    constructor
    · intro h
      have h₃ : (2 ^ n - 1) % 7 = 0 := h
      have h₄ : 2 ^ n % 7 = 1 := by
        omega
      exact h₄
    · intro h
      have h₃ : 2 ^ n % 7 = 1 := h
      have h₄ : (2 ^ n - 1) % 7 = 0 := by
        omega
      exact h₄
  have h_pow_mod : 2 ^ n % 7 = 2 ^ (n % 3) % 7 := by
    rw [Nat.pow_mod]
    rw [Nat.pow_mod]
    skip
    rw [Nat.pow_mod]
    skip
    rw [Nat.pow_mod]
    rw [Nat.pow_mod]
    skip
    rw [Nat.pow_mod]
    simp [Nat.pow_mod, Nat.mul_mod, Nat.mod_mod_of_dvd]
    rw [Nat.pow_mod]
    skip
    simpa [Nat.mod_eq_of_lt (by norm_num : (2 : ℕ) < 7)] using (two_pow_mod_seven n)
  have h_cases : 2 ^ (n % 3) % 7 = 1 ↔ n % 3 = 0 := by
    have h₁ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h₁ with (h | h | h) <;> simp [h, pow_succ, Nat.mul_mod, Nat.pow_mod]
    <;> norm_num <;> omega
  have h_dvd_iff_mod : 3 ∣ n ↔ n % 3 = 0 := by
    omega
  exact ⟨fun h => by simp_all [h_mod, h_pow_mod, h_cases, h_dvd_iff_mod], fun h => by simp_all [h_mod, h_pow_mod, h_cases, h_dvd_iff_mod]⟩

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h1 : (2 ^ n + 1) % 7 = 0 := by
    rw [Nat.dvd_iff_mod_eq_zero] at h
    exact h
  have h2 : (2 ^ n + 1) % 7 = 0 → False := by
    have h3 : 2 ^ n % 7 = 2 ^ (n % 3) % 7 := two_pow_mod_seven n
    have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h4 with (h | h | h) <;>
      simp [h, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at h3 h1 ⊢ <;>
      norm_num at h3 h1 ⊢ <;>
      omega
  exact h2 h1
