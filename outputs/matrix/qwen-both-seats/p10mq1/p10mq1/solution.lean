import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6
/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Prove that 6 is in the set: 6! < 3^6
    rw [p10_answer]
    norm_num [Nat.factorial]
  intro n hn
  have h : n < 7 := by
    by_contra h'
    have h'' : n ≥ 7 := by omega
    have h1 : Nat.factorial n ≥ 3 ^ n := by
      have h2 : ∀ k, k ≥ 7 → Nat.factorial k ≥ 3 ^ k := by
        intro k hk
        induction' hk with k hk IH
        · norm_num [Nat.factorial]
        · simp_all [Nat.factorial_succ, pow_succ]
          nlinarith [pow_pos (by norm_num : (0 : ℕ) < 3) k]
      exact h2 n h''
    have h3 : Nat.factorial n < 3 ^ n := hn
    linarith
    <;> omega

  rw [p10_answer] at *
  omega

