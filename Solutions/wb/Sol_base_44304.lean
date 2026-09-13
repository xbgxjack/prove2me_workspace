import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

/-- AM-GM for three positive reals with product at least one. -/
private theorem amgm3 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : 1 ≤ x*y*z) :
    3 ≤ x + y + z := by
  have h1 : 27 * (x*y*z) ≤ (x + y + z)^3 := by
    nlinarith [mul_nonneg hx.le (sq_nonneg (y - z)), mul_nonneg hy.le (sq_nonneg (z - x)),
      mul_nonneg hz.le (sq_nonneg (x - y)),
      mul_nonneg (by linarith : (0:ℝ) ≤ x + y + z) (sq_nonneg (x - y)),
      mul_nonneg (by linarith : (0:ℝ) ≤ x + y + z) (sq_nonneg (y - z)),
      mul_nonneg (by linarith : (0:ℝ) ≤ x + y + z) (sq_nonneg (z - x))]
  have h2 : (27:ℝ) ≤ (x + y + z)^3 := by nlinarith [h1, h]
  by_contra hcon
  push_neg at hcon
  have hs : 0 < x + y + z := by linarith
  nlinarith [h2, hs, sq_nonneg (x + y + z)]

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (d + a ^ 2) / (d + b * c) + (d + b ^ 2) / (d + c * a) + (d + c ^ 2) / (d + a * b) ≥ 3 := by
  have p1 : (0:ℝ) < d + b * c := by positivity
  have p2 : (0:ℝ) < d + c * a := by positivity
  have p3 : (0:ℝ) < d + a * b := by positivity
  have hprod : 1 ≤ ((d + a^2)/(d + b*c)) * ((d + b^2)/(d + c*a)) * ((d + c^2)/(d + a*b)) := by
    have e : ((d + a^2)/(d + b*c)) * ((d + b^2)/(d + c*a)) * ((d + c^2)/(d + a*b))
        = ((d + a^2) * ((d + b^2) * (d + c^2))) / ((d + b*c) * ((d + c*a) * (d + a*b))) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity), one_mul]
    nlinarith [mul_nonneg (sq_nonneg d) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg d) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg d) (sq_nonneg (c - a)),
      mul_nonneg hd.le (sq_nonneg (a*b - b*c)),
      mul_nonneg hd.le (sq_nonneg (b*c - c*a)),
      mul_nonneg hd.le (sq_nonneg (c*a - a*b))]
  exact amgm3 _ _ _ (by positivity) (by positivity) (by positivity) hprod
