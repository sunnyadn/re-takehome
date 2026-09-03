import Mathlib

/-- The last two digits of `7 ^ 2026`. Must be a numeric literal. -/
abbrev p06_answer : ℕ := 49
/-- Compute `7 ^ 2026 % 100`. -/
theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by
  norm_num
  have h20 : 7 ^ 20 % 100 = 1 := by
    rfl
  have hexp : 7 ^ 2026 % 100 = 7 ^ 6 % 100 := by
    have h : 2026 = 20 * 101 + 6 := by norm_num
    rw [h, pow_add, pow_mul, Nat.pow_mod]
    simp [h20, Nat.mul_mod, Nat.add_mod]
  have h6 : 7 ^ 6 % 100 = 49 := by
    rfl
  calc
    7 ^ 2026 % 100 = 7 ^ 6 % 100 := hexp
    _ = 49 := h6
