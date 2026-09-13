import Mathlib
open Real Nat

theorem solution (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : (2 * a ^ 2 + 1) * (2 * b ^ 2 + 1) * (2 * c ^ 2 + 1) ≥ 3 * (a + b + c) ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a*b - 1), sq_nonneg (b*c - 1), sq_nonneg (c*a - 1),
    mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb),
    mul_nonneg (sub_nonneg.2 hb) (sub_nonneg.2 hc),
    mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 ha),
    sq_nonneg (a*b*c - 1), sq_nonneg (a + b + c - 3)]
