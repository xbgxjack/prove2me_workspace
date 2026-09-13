import Mathlib
open Real Nat

theorem solution (a b c : ℝ) (ha : a^2 + 2 * b = 7) (hb : b^2 + 4 * c = -7) : c^2 + 6 * a ≥ -14 := by
  nlinarith [sq_nonneg (a + 3), sq_nonneg (b + 1), sq_nonneg (c + 2)]
