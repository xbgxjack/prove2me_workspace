import Mathlib
open Real Nat

theorem solution (a b : ℝ) (h : a^4 + b^4 + a^2 * b^2 = 60) :
  4 * a^2 + 4 * b^2 - a * b ≥ 30 := by
  nlinarith [sq_nonneg (a*b - 2), sq_nonneg (a - b), sq_nonneg (a + b),
    sq_nonneg (a^2 + b^2), sq_nonneg (a*b), sq_nonneg (a^2 - b^2)]
