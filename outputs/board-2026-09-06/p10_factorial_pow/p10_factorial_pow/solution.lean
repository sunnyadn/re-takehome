import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6
/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem vm_cell_33 (h_mem : p10_answer ∈ {n | n.factorial < (3 : ℕ) ^ n}) ⦃n : ℕ⦄ (hn : n ∈ {n | n.factorial < (3 : ℕ) ^ n}) (h_main : ∀ (n : ℕ), (7 : ℕ) ≤ n → ¬n.factorial < (3 : ℕ) ^ n) : n ≤ p10_answer := by
  exact Nat.le_of_not_lt fun a => h_main n a hn

theorem vm_cell_20 (h_mem : p10_answer ∈ {n | n.factorial < (3 : ℕ) ^ n}) ⦃n : ℕ⦄ (hn : n ∈ {n | n.factorial < (3 : ℕ) ^ n}) : n ≤ p10_answer := by
  have h_main : ∀ n, 7 ≤ n → ¬(n.factorial < 3 ^ n) := by
    intro n hn
    have h1 : 3 ^ n ≤ n.factorial := by
      induction' hn with k hk IH
      · norm_num [Nat.factorial]
      · cases k with
        | zero => contradiction
        | succ k' =>
          simp_all [Nat.factorial_succ, pow_succ]
          nlinarith [pow_pos (by norm_num : (0 : ℕ) < 3) k']
    exact fun h => lt_irrefl _ (h1.trans_lt h)
  first | (exact vm_cell_33 ‹_›) | (exact vm_cell_33 h_mem) | (apply vm_cell_33 <;> assumption)

theorem vm_cell_9 (h_mem : p10_answer ∈ {n | n.factorial < (3 : ℕ) ^ n}) : IsGreatest {n | n.factorial < (3 : ℕ) ^ n} p10_answer := by
  refine ⟨h_mem, ?_⟩
  intro n hn
  first | (exact vm_cell_20 ‹_›) | (exact vm_cell_20 h_mem) | (apply vm_cell_20 <;> assumption)

theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  have h_mem : p10_answer ∈ {n : ℕ | Nat.factorial n < 3 ^ n} := by
    simp [p10_answer]
    decide
  first | (exact vm_cell_9 ‹_›) | (exact vm_cell_9 h_mem) | (apply vm_cell_9 <;> assumption)
