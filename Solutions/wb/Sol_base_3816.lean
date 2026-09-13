import Mathlib
open Real Nat

theorem solution (x y z: ℝ) (h : x ^ 4 + y ^ 4 + z ^ 4 = 3) :
  x ^ 2 * (x + y) + y ^ 2 * (y + z) + z ^ 2 * (z + x) ≥ -6 := by
  nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (z + 1),
    sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (z^2 - 1),
    sq_nonneg (x + y), sq_nonneg (y + z), sq_nonneg (z + x),
    sq_nonneg (x^2 + x), sq_nonneg (y^2 + y), sq_nonneg (z^2 + z)]
