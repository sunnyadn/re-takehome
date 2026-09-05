import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6
/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  rw [IsGreatest]
  constructor
  -- Part 1: Show that p10_answer (6) is in the set, i.e., 6! < 3^6
  · norm_num [p10_answer, Nat.factorial]
  -- Part 2: Show that for all n > 6, n! >= 3^n
  intro n hn
  have h_main : ∀ k, k > 6 → k.factorial ≥ 3 ^ k := by
    intro k hk
    induction' hk with k hk IH
    · norm_num [p10_answer, Nat.factorial]
    · cases k with
      | zero => contradiction
      | succ k' =>
        simp_all [Nat.factorial_succ, pow_succ]
        nlinarith [pow_pos (by norm_num : (0 : ℕ) < 3) k']
  by_contra h
  have h' : n > p10_answer := by omega
  have h_fact : n.factorial ≥ 3 ^ n := h_main n h'
  have h_lt : n.factorial < 3 ^ n := hn
  linarith
