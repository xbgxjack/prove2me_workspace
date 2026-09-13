import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

private theorem disc {x y z : ℝ} (h : x + y + z = 0) :
    27 * (x*y*z)^2 ≤ 4 * (-(x*y + y*z + z*x))^3 := by
  have hz : z = -x - y := by linarith
  subst hz
  nlinarith [sq_nonneg ((x - y) * (y - (-x - y)) * ((-x - y) - x))]

theorem solution (a b c : ℝ) (habc : a + b + c = 0) : a^2 * b^2 + a^2 * c^2 + b^2 * c^2 + 3 ≥ 6 * a * b * c := by
  have hc : c = -a - b := by linarith
  subst hc
  have hd : 27 * (a*b*(-a-b))^2 ≤ 4 * (-(a*b + b*(-a-b) + (-a-b)*a))^3 :=
    disc (x := a) (y := b) (z := -a-b) (by ring)
  have hq0 : (0:ℝ) ≤ a^2 + a*b + b^2 := by nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
  have hpos : (0:ℝ) ≤ (a^2 + a*b + b^2 - 3)^2 * (3*(a^2 + a*b + b^2)^2 + 2*(a^2 + a*b + b^2) + 3) := by
    apply mul_nonneg (sq_nonneg _)
    nlinarith [sq_nonneg (a^2 + a*b + b^2), hq0]
  nlinarith [hd, hq0, hpos, sq_nonneg (a*b*(a+b))]
