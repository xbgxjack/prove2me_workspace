import Mathlib
open Real Nat

theorem solution (a : ℝ) : (1 + |a| + a^2)^3 ≥ (1 + |a|)^3 * (1 + |a|^3) := by
  have ht : (0:ℝ) ≤ |a| := abs_nonneg a
  have h2 : a^2 = |a|^2 := (sq_abs a).symm
  rw [h2]
  nlinarith [ht, mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht,
    mul_nonneg (mul_nonneg (mul_nonneg ht ht) ht) ht]
