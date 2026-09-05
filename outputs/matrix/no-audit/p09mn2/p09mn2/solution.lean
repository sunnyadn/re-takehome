import Mathlib

theorem two_pow_three_modEq_one : Nat.ModEq 7 (2 ^ 3) 1 := by
  rfl

theorem mod7_pow2_pattern (n : ℕ) : 2 ^ n % 7 = if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := by
  induction' n with n ih
  · simp [Nat.pow_zero]
  · cases n with
    | zero => simp [Nat.pow_succ, Nat.mul_mod, Nat.mod_eq_of_lt]
    | succ n =>
      have h := ih
      simp [Nat.pow_succ, Nat.mul_mod, Nat.add_mod, Nat.mod_mod_of_dvd] at *
      split_ifs at * <;>
        (try omega) <;>
        (try {
          have h1 : (n + 2) % 3 = 0 ∨ (n + 2) % 3 = 1 ∨ (n + 2) % 3 = 2 := by omega
          rcases h1 with (h1 | h1 | h1) <;>
            simp [h1, Nat.mul_mod, Nat.mod_mod_of_dvd] at * <;>
            omega
        }) <;>
        (try {
          have h1 : (n + 2) % 3 = 0 ∨ (n + 2) % 3 = 1 ∨ (n + 2) % 3 = 2 := by omega
          rcases h1 with (h1 | h1 | h1) <;>
            simp [h1, Nat.mul_mod, Nat.mod_mod_of_dvd] at * <;>
            omega
        }) <;>
        (try {
          have h1 : (n + 2) % 3 = 0 ∨ (n + 2) % 3 = 1 ∨ (n + 2) % 3 = 2 := by omega
          rcases h1 with (h1 | h1 | h1) <;>
            simp [h1, Nat.mul_mod, Nat.mod_mod_of_dvd] at * <;>
            omega
        })

theorem two_pow_mod_7_cases (n : ℕ) : 2 ^ n % 7 = if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := by
  exact mod7_pow2_pattern n

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  case mp =>
    rw [← Nat.mod_add_div n 3]
    simp [pow_add, pow_mul, two_pow_mod_7_cases, Nat.mul_mod, Nat.pow_mod, Nat.add_mod, Nat.mod_mod]
    rw [Nat.dvd_iff_mod_eq_zero] at *
    rw [Nat.dvd_iff_mod_eq_zero] at *
    have h_mod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    intro h
    rcases h_mod with h0 | h1 | h2
    · -- case `n % 3 = 0`
      simpa [h0] using
        (by
          have : (n % 3 + 3 * (n / 3)) % 3 = (n % 3) % 3 := by
            simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_mul_left_mod, Nat.mod_mul_right_mod] using rfl
          simpa [h0] using this)
    case inr.inl =>
      have h_mod3 : (n % 3 + 3 * (n / 3)) % 3 = n % 3 := by
        simp [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
      rw [h_mod3]
      simp [h1]
      have h_val : (2 ^ (n % 3) * 8 ^ (n / 3)) % 7 = 2 := by
        have h1' : n % 3 = 1 := h1
        rw [h1']
        norm_num [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, two_pow_mod_7_cases]
        <;> simp_all [two_pow_mod_7_cases]
        <;> omega

      have h_contra : False := by
        have h3 : (2 ^ (n % 3) * 8 ^ (n / 3) - 1) % 7 = 0 := h
        have h4 : (2 ^ (n % 3) * 8 ^ (n / 3)) % 7 = 2 := h_val
        have h5 : (2 ^ (n % 3) * 8 ^ (n / 3) - 1) % 7 = 1 := by
          omega
        omega

      exact h_contra
    case inr.inr =>
      have h_mod3 : (n % 3 + 3 * (n / 3)) % 3 = n % 3 := by
        norm_num
      have h_contra : False := by
        have h_val : (2 ^ (n % 3) * 8 ^ (n / 3)) % 7 = 4 := by
          have h1 : n % 3 = 2 := h2
          rw [h1]
          norm_num [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, two_pow_mod_7_cases]
          <;> simp_all [two_pow_mod_7_cases]
          <;> omega

        have h_contra : False := by
          have h3 : (2 ^ (n % 3) * 8 ^ (n / 3) - 1) % 7 = 0 := h
          have h4 : (2 ^ (n % 3) * 8 ^ (n / 3)) % 7 = 4 := h_val
          have h5 : (2 ^ (n % 3) * 8 ^ (n / 3) - 1) % 7 = 3 := by
            omega
          omega

        exact h_contra
      trivial
  case mpr =>
    intro h3
    have hmod : n % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
    have hval : 2 ^ n % 7 = 1 := by
      simpa [two_pow_mod_7_cases, hmod]
    apply (Nat.dvd_iff_mod_eq_zero).mpr
    omega

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h_mod : 2 ^ n % 7 = if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := two_pow_mod_7_cases n
  rw [Nat.dvd_iff_mod_eq_zero] at h
  have h_sum : (2 ^ n + 1) % 7 = 0 := by simpa using h
  have h_case : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h_case with (h_case | h_case | h_case) <;> simp [h_case, h_mod, Nat.add_mod, Nat.mod_mod] at h_sum <;> omega

