import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6
/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  have h_mem : p10_answer ∈ {n : ℕ | Nat.factorial n < 3 ^ n} := by
    simp [p10_answer]
    decide
  refine ⟨h_mem, ?_⟩
  intro n hn
  have h_bound : ∀ k ≥ 7, k.factorial ≥ 3 ^ k := by
    intro k hk
    induction' hk with k hk IH
    · norm_num [Nat.factorial]
    · simp_all [Nat.factorial_succ, pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℕ) < 3) k]
  have h_cases : n < 7 := by
    by_contra h
    have h_ge : n ≥ 7 := by omega
    have h_fact : n.factorial ≥ 3 ^ n := h_bound n h_ge
    have hlt : n.factorial < 3 ^ n := by
      simpa using hn
    have hle : 3 ^ n ≤ n.factorial := h_fact
    have : n.factorial < n.factorial := lt_of_lt_of_le hlt hle
    exact lt_irrefl _ this
  linarith
