import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

/-- Discriminant bound for a cubic with roots summing to zero:
`4(-e₂)³ - 27e₃² = ((x-y)(y-z)(z-x))² ≥ 0`. -/
theorem disc {x y z : ℝ} (h : x + y + z = 0) :
    27 * (x*y*z)^2 ≤ 4 * (-(x*y + y*z + z*x))^3 := by
  have hz : z = -x - y := by linarith
  subst hz
  nlinarith [sq_nonneg ((x - y) * (y - (-x - y)) * ((-x - y) - x))]

/- base_11560 : with c = -a-b the claim is q² + 6r + 3 ≥ 0 where
   q = a²+ab+b² ≥ 0 and r = ab(a+b), and 27r² ≤ 4q³.
   If 6r < -(q²+3) then 36r² > (q²+3)², while 36r² ≤ 16q³/3, giving
   3(q²+3)² < 16q³, i.e. (q-3)²(3q²+2q+3) < 0 — impossible. -/
theorem s11560 (a b c : ℝ) (habc : a + b + c = 0) :
    a^2 * b^2 + a^2 * c^2 + b^2 * c^2 + 3 ≥ 6 * a * b * c := by
  have hc : c = -a - b := by linarith
  subst hc
  have hd : 27 * (a*b*(-a-b))^2 ≤ 4 * (-(a*b + b*(-a-b) + (-a-b)*a))^3 :=
    disc (x := a) (y := b) (z := -a-b) (by ring)
  have hq0 : (0:ℝ) ≤ a^2 + a*b + b^2 := by nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
  have hpos : (0:ℝ) ≤ (a^2 + a*b + b^2 - 3)^2 * (3*(a^2 + a*b + b^2)^2 + 2*(a^2 + a*b + b^2) + 3) := by
    apply mul_nonneg (sq_nonneg _)
    nlinarith [sq_nonneg (a^2 + a*b + b^2), hq0]
  nlinarith [hd, hq0, hpos, sq_nonneg (a*b*(a+b))]

/- base_31532 : shift x = a+2, y = b+2, z = c+2 so x+y+z = 0.  With
   m = -(xy+yz+zx) ≥ 0 and e₃ = xyz the expression is m² + 24m + 24e₃, and
   27e₃² ≤ 4m³.  Here 3m² - 112m + 1728 > 0 always, so there is slack. -/
theorem s31532 (a b c : ℝ) (h : a + b + c = -6) :
    a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 12 * a * b * c + 48 ≥ 0 := by
  have hd : 27 * ((a+2)*(b+2)*(c+2))^2
      ≤ 4 * (-((a+2)*(b+2) + (b+2)*(c+2) + (c+2)*(a+2)))^3 :=
    disc (x := a+2) (y := b+2) (z := c+2) (by linarith)
  have hm0 : (0:ℝ) ≤ -((a+2)*(b+2) + (b+2)*(c+2) + (c+2)*(a+2)) := by
    nlinarith [sq_nonneg (a+2), sq_nonneg (b+2), sq_nonneg (c+2), sq_nonneg (a+b+c+6)]
  have hslack : (0:ℝ) ≤ 3 * (-((a+2)*(b+2) + (b+2)*(c+2) + (c+2)*(a+2)))^2
      - 112 * (-((a+2)*(b+2) + (b+2)*(c+2) + (c+2)*(a+2))) + 1728 := by
    nlinarith [sq_nonneg (3 * (-((a+2)*(b+2) + (b+2)*(c+2) + (c+2)*(a+2))) - 56), hm0]
  nlinarith [hd, hm0, hslack, sq_nonneg ((a+2)*(b+2)*(c+2))]
