import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6
/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  have h_mem : p10_answer ∈ {n : ℕ | Nat.factorial n < 3 ^ n} := by
    simp [p10_answer]
    decide
  have h_upper : ∀ n, n ∈ {n : ℕ | n.factorial < 3 ^ n} → n ≤ p10_answer := by
    intro n hn
    by_cases hle : n ≤ p10_answer
    · exact hle
    · have hgt : p10_answer < n := Nat.lt_of_not_ge hle
      have hseven : 7 ≤ n := by
        have : (p10_answer + 1) ≤ n := Nat.succ_le_of_lt hgt
        simpa [p10_answer] using this
      have hpow : 3 ^ n ≤ n.factorial := by
        have : ∀ m ≥ 7, 3 ^ m ≤ m.factorial := by
          intro m hm
          have hm7 : 7 ≤ m := hm
          have : (m.succ).factorial = (m.succ) * m.factorial := by
            simpa [Nat.succ_eq_add_one, Nat.factorial_succ] using rfl
          induction' hm with m ih IH
          · norm_num [Nat.factorial]
          · simp_all [Nat.factorial_succ, Nat.pow_succ, mul_comm]
            nlinarith
        exact this n hseven
      have : n.factorial < 3 ^ n := hn
      exact (lt_of_lt_of_le this hpow).false.elim
  exact ⟨h_mem, h_upper⟩
