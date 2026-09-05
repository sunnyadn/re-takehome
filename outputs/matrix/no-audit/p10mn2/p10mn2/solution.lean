import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6
/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  rw [IsGreatest]
  constructor
  · -- Prove 6 is in the set: 6! < 3^6
    norm_num [Nat.factorial, p10_answer]
  intro n hn
  rw [Set.mem_setOf_eq] at hn
  have h : n ≤ 6 := by
    by_contra h'
    have h'' : n ≥ 7 := by omega
    have h3 : 3 ^ n ≤ n.factorial := by
      have h4 : ∀ k, 7 ≤ k → 3 ^ k ≤ k.factorial := by
        intro k hk
        induction' hk with k hk IH
        · norm_num [Nat.factorial]
        · simp_all [Nat.factorial_succ, pow_succ]
          nlinarith
      exact h4 n h''
    linarith
  exact h
