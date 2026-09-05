import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6
/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem vm_cell_4 : p10_answer ∈ upperBounds {n | n.factorial < (3 : ℕ) ^ n} := by
  intro n hn
  have hcases : n ≤ 6 ∨ 7 ≤ n := by
    have h := Nat.lt_or_ge n 7
    cases h with
    | inl hlt =>
        left
        exact Nat.le_of_lt_succ hlt
    | inr hge =>
        right
        exact hge
  cases hcases with
  | inl hle =>
    have : n ≤ 6 := by linarith
    simpa [p10_answer] using this
  | inr hge =>
    have h7 : 7 ≤ n := hge
    have hfail : ¬(n.factorial < 3 ^ n) := by
      induction' h7 with k hk IH
      · norm_num [Nat.factorial]
      · simp_all [Nat.factorial_succ, pow_succ]
        nlinarith [pow_pos (by norm_num : (0 : ℕ) < 3) k]
    exact absurd hn hfail

theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  rw [IsGreatest]
  constructor
  · -- Prove 6 ∈ {n | n! < 3^n}
    norm_num [Nat.factorial]
  exact vm_cell_4
