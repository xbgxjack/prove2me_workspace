import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

private theorem disc {x y z : ℝ} (h : x + y + z = 0) :
    27 * (x*y*z)^2 ≤ 4 * (-(x*y + y*z + z*x))^3 := by
  have hz : z = -x - y := by linarith
  subst hz
  nlinarith [sq_nonneg ((x - y) * (y - (-x - y)) * ((-x - y) - x))]

private theorem key (M E : ℝ) (hm0 : 0 ≤ M) (hd : 27 * E^2 ≤ 4 * M^3) :
    0 ≤ M^2 + 24*M + 24*E := by
  have hslack : (0:ℝ) ≤ 3 * M^2 - 112 * M + 1728 := by
    nlinarith [sq_nonneg (3 * M - 56), hm0]
  nlinarith [hd, hm0, mul_nonneg (sq_nonneg M) hslack, sq_nonneg E, sq_nonneg (M^2 + 24*M)]

theorem solution (a b c : ℝ) (h : a + b + c = -6) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 12 * a * b * c + 48 ≥ 0 := by
  have hc : c = -6 - a - b := by linarith
  subst hc
  have hd : 27 * ((a+2)*(b+2)*((-6 - a - b)+2))^2
      ≤ 4 * (-((a+2)*(b+2) + (b+2)*((-6 - a - b)+2) + ((-6 - a - b)+2)*(a+2)))^3 :=
    disc (x := a+2) (y := b+2) (z := (-6 - a - b)+2) (by ring)
  have hm0 : (0:ℝ) ≤ -((a+2)*(b+2) + (b+2)*((-6 - a - b)+2) + ((-6 - a - b)+2)*(a+2)) := by
    nlinarith [sq_nonneg (a+2), sq_nonneg (b+2), sq_nonneg (a+b+4)]
  have hk := key _ _ hm0 hd
  nlinarith [hk]
