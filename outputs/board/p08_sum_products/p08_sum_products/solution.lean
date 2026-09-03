import Mathlib

/-- Positive reals `a, b, c` with `a + b + c = 3` satisfy `a*b + b*c + c*a ≤ 3`. -/
theorem p08_sum_products (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) : a * b + b * c + c * a ≤ 3 := by
  have h_sq : (a + b + c) ^ 2 = 9 := by
    rw [h]
    norm_num
  have h_main : a * b + b * c + c * a ≤ 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  exact h_main
