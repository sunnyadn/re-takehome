import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6
/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem vm_cell_27 : p10_answer ∈ upperBounds {n | n.factorial < (3 : ℕ) ^ n} := by
  intro n hn
  have h7 : 7 ≤ n → ¬ (n.factorial < 3 ^ n) := by
    intro hle
    have h3 : 3 ≤ n := by
      first
      | (trace "closer 0"; rfl; done)
      | (trace "closer 1"; trivial; done)
      | (trace "closer 2"; assumption; done)
      | (trace "closer 3"; norm_num; done)
      | (trace "closer 4"; simp; done)
      | (trace "closer 5"; omega; done)
      | (trace "closer 6"; positivity; done)
      | (trace "closer 7"; ring; done)
      | (trace "closer 8"; linarith; done)
      | (trace "closer 9"; nlinarith; done)
      | (trace "closer 10"; field_simp; ring; done)
      | (trace "closer 11"; simp; omega; done)
      | (trace "closer 12"; norm_num; omega; done)
      | (trace "closer 13"; constructor <;> norm_num; done)
      | (trace "closer 14"; simp_all; done)
      | (trace "closer 15"; aesop; done)
      | (trace "closer 16"; decide; done)
      | (trace "closer 17"; gcongr; done)
      | (trace "closer 18"; bound; done)
      | (trace "closer 19"; norm_cast; done)
      | (trace "closer 20"; push_cast; ring; done)
      | (trace "closer 21"; interval_cases <;> norm_num; done)
      | (trace "closer 22"; exact le_refl _; done)
      | (trace "closer 23"; tauto; done)
      | (trace "closer 24"; subst_vars <;> omega; done)
      | (trace "closer 25"; subst_vars <;> ring; done)
      | (trace "closer 26"; subst_vars <;> nlinarith; done)
      | (trace "closer 27"; constructor <;> omega; done)
      | (trace "closer 28"; refine ⟨?_, ?_⟩ <;> norm_num; done)
      | (trace "closer 29"; simp_all <;> omega; done)
      | (trace "closer 30"; zify; omega; done)
      | (trace "closer 31"; push_cast; omega; done)
      | (trace "closer 32"; ring_nf; omega; done)
      | (trace "closer 33"; ring_nf; nlinarith; done)
      | (trace "closer 34"; interval_cases <;> omega; done)
      | (trace "closer 35"; simp_arith; done)
      | (trace "closer 36"; constructor <;> simp; done)
      | (trace "closer 37"; refine ⟨?_, ?_, ?_⟩ <;> norm_num; done)
      | (trace "closer 38"; decide <;> norm_num; done)
      | (trace "closer 39"; field_simp; nlinarith; done)
      | (trace "closer 40"; rify; nlinarith; done)
      | (trace "closer 41"; omega <;> norm_num; done)
    have hfact : ∀ k, 7 ≤ k → 3 ^ k ≤ k.factorial := by
      have h_ind : ∀ k, 7 ≤ k → 3 ^ k ≤ k.factorial := by
        intro k hk
        induction' hk with k hk IH
        · norm_num [Nat.factorial]
        · simp_all [Nat.factorial_succ, pow_succ, Nat.mul_assoc]
          nlinarith [pow_pos (by norm_num : (0 : ℕ) < 3) k]
      first
      | (trace "closer 0"; rfl; done)
      | (trace "closer 1"; trivial; done)
      | (trace "closer 2"; assumption; done)
      | (trace "closer 3"; norm_num; done)
      | (trace "closer 4"; simp; done)
      | (trace "closer 5"; omega; done)
      | (trace "closer 6"; positivity; done)
      | (trace "closer 7"; ring; done)
      | (trace "closer 8"; linarith; done)
      | (trace "closer 9"; nlinarith; done)
      | (trace "closer 10"; field_simp; ring; done)
      | (trace "closer 11"; simp; omega; done)
      | (trace "closer 12"; norm_num; omega; done)
      | (trace "closer 13"; constructor <;> norm_num; done)
      | (trace "closer 14"; simp_all; done)
      | (trace "closer 15"; aesop; done)
      | (trace "closer 16"; decide; done)
      | (trace "closer 17"; gcongr; done)
      | (trace "closer 18"; bound; done)
      | (trace "closer 19"; norm_cast; done)
      | (trace "closer 20"; push_cast; ring; done)
      | (trace "closer 21"; interval_cases <;> norm_num; done)
      | (trace "closer 22"; exact le_refl _; done)
      | (trace "closer 23"; tauto; done)
      | (trace "closer 24"; subst_vars <;> omega; done)
      | (trace "closer 25"; subst_vars <;> ring; done)
      | (trace "closer 26"; subst_vars <;> nlinarith; done)
      | (trace "closer 27"; constructor <;> omega; done)
      | (trace "closer 28"; refine ⟨?_, ?_⟩ <;> norm_num; done)
      | (trace "closer 29"; simp_all <;> omega; done)
      | (trace "closer 30"; zify; omega; done)
      | (trace "closer 31"; push_cast; omega; done)
      | (trace "closer 32"; ring_nf; omega; done)
      | (trace "closer 33"; ring_nf; nlinarith; done)
      | (trace "closer 34"; interval_cases <;> omega; done)
      | (trace "closer 35"; simp_arith; done)
      | (trace "closer 36"; constructor <;> simp; done)
      | (trace "closer 37"; refine ⟨?_, ?_, ?_⟩ <;> norm_num; done)
      | (trace "closer 38"; decide <;> norm_num; done)
      | (trace "closer 39"; field_simp; nlinarith; done)
      | (trace "closer 40"; rify; nlinarith; done)
      | (trace "closer 41"; omega <;> norm_num; done)
    rw [not_lt]
    first
    | (trace "closer 0"; rfl; done)
    | (trace "closer 1"; trivial; done)
    | (trace "closer 2"; assumption; done)
    | (trace "closer 3"; norm_num; done)
    | (trace "closer 4"; simp; done)
    | (trace "closer 5"; omega; done)
    | (trace "closer 6"; positivity; done)
    | (trace "closer 7"; ring; done)
    | (trace "closer 8"; linarith; done)
    | (trace "closer 9"; nlinarith; done)
    | (trace "closer 10"; field_simp; ring; done)
    | (trace "closer 11"; simp; omega; done)
    | (trace "closer 12"; norm_num; omega; done)
    | (trace "closer 13"; constructor <;> norm_num; done)
    | (trace "closer 14"; simp_all; done)
    | (trace "closer 15"; aesop; done)
    | (trace "closer 16"; decide; done)
    | (trace "closer 17"; gcongr; done)
    | (trace "closer 18"; bound; done)
    | (trace "closer 19"; norm_cast; done)
    | (trace "closer 20"; push_cast; ring; done)
    | (trace "closer 21"; interval_cases <;> norm_num; done)
    | (trace "closer 22"; exact le_refl _; done)
    | (trace "closer 23"; tauto; done)
    | (trace "closer 24"; subst_vars <;> omega; done)
    | (trace "closer 25"; subst_vars <;> ring; done)
    | (trace "closer 26"; subst_vars <;> nlinarith; done)
    | (trace "closer 27"; constructor <;> omega; done)
    | (trace "closer 28"; refine ⟨?_, ?_⟩ <;> norm_num; done)
    | (trace "closer 29"; simp_all <;> omega; done)
    | (trace "closer 30"; zify; omega; done)
    | (trace "closer 31"; push_cast; omega; done)
    | (trace "closer 32"; ring_nf; omega; done)
    | (trace "closer 33"; ring_nf; nlinarith; done)
    | (trace "closer 34"; interval_cases <;> omega; done)
    | (trace "closer 35"; simp_arith; done)
    | (trace "closer 36"; constructor <;> simp; done)
    | (trace "closer 37"; refine ⟨?_, ?_, ?_⟩ <;> norm_num; done)
    | (trace "closer 38"; decide <;> norm_num; done)
    | (trace "closer 39"; field_simp; nlinarith; done)
    | (trace "closer 40"; rify; nlinarith; done)
    | (trace "closer 41"; omega <;> norm_num; done)
  by_contra hnot
  have h6lt : 6 < n := Nat.lt_of_not_ge hnot
  have h7le : 7 ≤ n := Nat.succ_le_of_lt h6lt
  have hcond : n.factorial < 3 ^ n := by
    simpa [Set.mem_setOf_eq] using hn
  exact (h7 h7le) hcond

theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Prove that 6! < 3^6
      norm_num [Nat.factorial]
  exact vm_cell_27

