import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6
/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Prove 6! < 3^6
    norm_num [p10_answer, Nat.factorial]
  intro n hn
  by_contra h
  have h₁ : n > p10_answer := by
    omega
  have h₂ : n ≥ 7 := by
    norm_num [p10_answer] at h₁
    omega
  have h₃ : n.factorial ≥ 3 ^ n := by
    have h₄ : ∀ k, 7 ≤ k → k.factorial ≥ 3 ^ k := by
      intro k hk
      induction' hk with k hk IH
      · norm_num [p10_answer]
      · simp_all [Nat.factorial_succ, pow_succ]
        nlinarith [pow_pos (by norm_num : (0 : ℕ) < 3) k]
    exact h₄ n h₂
  have h₄ : False := by
    simp_all <;> omega
  trivial

