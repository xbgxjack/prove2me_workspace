import Mathlib
open Real Nat

theorem solution (a b c d x : ℝ) (a2c2_leq_4b : a^2 + c^2 ≤ 4*b) : x^4 + a*x^3 + b*x^2 + c*x + 1 ≥ 0 := by
  nlinarith [sq_nonneg (2*x^2 + a*x), sq_nonneg (c*x + 2),
    mul_nonneg (sub_nonneg.2 a2c2_leq_4b) (sq_nonneg x)]
