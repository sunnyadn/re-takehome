import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 8000
set_option exponentiation.threshold 4000



/-- The last two digits of `7 ^ 2026`. Must be a numeric literal. -/
abbrev p06_answer : ℕ := 49
/-- Compute `7 ^ 2026 % 100`. -/
theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by
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
