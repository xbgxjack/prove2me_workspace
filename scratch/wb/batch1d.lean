import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

theorem disc {x y z : ℝ} (h : x + y + z = 0) :
    27 * (x*y*z)^2 ≤ 4 * (-(x*y + y*z + z*x))^3 := by
  have hz : z = -x - y := by linarith
  subst hz
  nlinarith [sq_nonneg ((x - y) * (y - (-x - y)) * ((-x - y) - x))]

/- base_31532.  Shift x = a+2 etc. so x+y+z = 0; with m = -(xy+yz+zx) ≥ 0 and
   e₃ = xyz the expression equals m² + 24m + 24e₃, and 27e₃² ≤ 4m³.
   If m² + 24m + 24e₃ < 0 then 576e₃² > (m²+24m)², so (256/3)m³ > m²(m+24)²,
   i.e. m²(3m² - 112m + 1728) < 0.  The quadratic has negative discriminant
   (112² < 4·3·1728), so that product is nonnegative — contradiction. -/
theorem s31532 (a b c : ℝ) (h : a + b + c = -6) :
    a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 12 * a * b * c + 48 ≥ 0 := by
  have hd : 27 * ((a+2)*(b+2)*(c+2))^2
      ≤ 4 * (-((a+2)*(b+2) + (b+2)*(c+2) + (c+2)*(a+2)))^3 :=
    disc (x := a+2) (y := b+2) (z := c+2) (by linarith)
  set M : ℝ := -((a+2)*(b+2) + (b+2)*(c+2) + (c+2)*(a+2)) with hM
  have hm0 : (0:ℝ) ≤ M := by
    rw [hM]; nlinarith [sq_nonneg (a+2), sq_nonneg (b+2), sq_nonneg (c+2), sq_nonneg (a+b+c+6)]
  have hslack : (0:ℝ) ≤ 3 * M^2 - 112 * M + 1728 := by
    nlinarith [sq_nonneg (3 * M - 56), hm0]
  have hprod : (0:ℝ) ≤ (3 * M^2 - 112 * M + 1728) * M^2 := mul_nonneg hslack (sq_nonneg M)
  nlinarith [hd, hm0, hprod, sq_nonneg ((a+2)*(b+2)*(c+2)), sq_nonneg M]
