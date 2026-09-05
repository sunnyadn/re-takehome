import Mathlib

theorem two_pow_mod_seven_eq_one_iff_three_dvd (n : ℕ) :
    (2 ^ n) % 7 = 1 ↔ 3 ∣ n := by
  constructor
  intro h
  have h_mod_3 : n % 3 = 0 := by
    have h_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h_cases with (h_r | h_r | h_r)
    · exact h_r
    · exfalso
      have h_val : 2 ^ n % 7 = 2 := by
        rw [← Nat.mod_add_div n 3]
        simp [h_r, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
        <;> norm_num
        <;> omega
      omega
    · exfalso
      have h_val : 2 ^ n % 7 = 4 := by
        rw [← Nat.mod_add_div n 3]
        simp [h_r, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
        <;> norm_num
        <;> omega
      omega
  omega
  rw [← Nat.mod_add_div n 3]
  simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
  <;> norm_num
  rw [← Nat.mod_add_div n 3]
  simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
  <;> norm_num
  rw [Nat.dvd_iff_mod_eq_zero] at *
  simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at *
  <;> norm_num at *
  simp_all

theorem mod7_pow2_cases (n : ℕ) : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := by
  have h : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := by
    have h_mod : ∀ k : ℕ, 2 ^ k % 7 = 1 ∨ 2 ^ k % 7 = 2 ∨ 2 ^ k % 7 = 4 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rcases ih with (h | h | h) <;>
          simp [pow_succ, Nat.mul_mod, h] at * <;>
          (try omega) <;>
          (try { left; omega }) <;>
          (try { right; left; omega }) <;>
          (try { right; right; omega })
    exact h_mod n
  exact h



/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  intro h
  case mp =>
    refine (two_pow_mod_seven_eq_one_iff_three_dvd n).mp ?_
    have hmod := Nat.mod_eq_zero_of_dvd h
    rw [← Nat.mod_add_div n 7] at hmod
    rw [← Nat.mod_add_div n 7] at hmod
    rw [← Nat.mod_add_div n 7] at hmod
    have hmod2 : (2 ^ n) % 7 = 1 := by
      have h1 : (2 ^ n - 1) % 7 = 0 := by
        rw [← Nat.mod_add_div n 7] at hmod
        simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, Nat.mod_eq_of_lt] at hmod ⊢
        <;> omega
      have h2 : (2 ^ n) % 7 = 1 := by
        have h3 : (2 ^ n - 1) % 7 = 0 := h1
        have h4 : (2 ^ n) % 7 = 1 := by
          have h5 : 2 ^ n ≥ 1 := by
            apply Nat.one_le_pow
            norm_num
          have h6 : (2 ^ n - 1 + 1) % 7 = 1 := by
            omega
          omega
        exact h4
      exact h2
    exact hmod2
  case mpr =>
    rw [← Nat.mod_add_div n 3]
    intro h
    have hmod : (2 ^ (n % 3 + 3 * (n / 3))) % 7 = 1 :=
      (two_pow_mod_seven_eq_one_iff_three_dvd _).mpr h
    omega

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h_cases : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := by
    apply mod7_pow2_cases
  rcases h_cases with (h_case | h_case | h_case)
  · -- Case 2^n ≡ 1 (mod 7)
    have h_sum : (2 ^ n + 1) % 7 = 2 := by
      rw [← Nat.mod_add_div (2 ^ n) 7]
      simp [h_case, Nat.add_mod, Nat.mod_mod]
      <;> norm_num
    omega
  · -- Case 2^n ≡ 2 (mod 7)
    have h_sum : (2 ^ n + 1) % 7 = 3 := by
      rw [← Nat.mod_add_div (2 ^ n) 7]
      simp [h_case, Nat.add_mod, Nat.mod_mod]
      <;> norm_num
    omega
  · -- Case 2^n ≡ 4 (mod 7)
    have h_sum : (2 ^ n + 1) % 7 = 5 := by
      rw [← Nat.mod_add_div (2 ^ n) 7]
      simp [h_case, Nat.add_mod, Nat.mod_mod]
      <;> norm_num
    omega

