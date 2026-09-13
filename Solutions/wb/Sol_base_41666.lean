import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

theorem solution (w x y z : ℝ) (hw : 0 < w) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (w^4 / z + x^4 / w + y^4 / x + z^4 / y) ≥ w * z^2 + x * w^2 + y * x^2 + z * y^2 := by
  have hT : (0:ℝ) < w + x + y + z := by linarith
  set S : ℝ := w^2 + x^2 + y^2 + z^2 with hS
  set T : ℝ := w + x + y + z with hTdef
  set t : ℝ := S / T with htdef
  have hT0 : T ≠ 0 := ne_of_gt hT
  have htT : t * T = S := by rw [htdef]; field_simp
  have step : ∀ a b : ℝ, 0 < b → 2*a^2*t - t^2*b ≤ a^4/b := by
    intro a b hb
    rw [le_div_iff₀ hb]
    nlinarith [mul_nonneg (sq_nonneg (a^2 - t*b)) hb.le, sq_nonneg (a^2 - t*b)]
  have hsum : 2*t*S - t^2*T ≤ w^4/z + x^4/w + y^4/x + z^4/y := by
    have a1 := step w z hz
    have a2 := step x w hw
    have a3 := step y x hx
    have a4 := step z y hy
    have e : 2*t*S - t^2*T
        = (2*w^2*t - t^2*z) + (2*x^2*t - t^2*w) + (2*y^2*t - t^2*x) + (2*z^2*t - t^2*y) := by
      rw [hS, hTdef]; ring
    rw [e]; linarith
  have hpoly : (w*z^2 + x*w^2 + y*x^2 + z*y^2) * T ≤ S^2 := by
    rw [hS, hTdef]
    nlinarith [sq_nonneg (w - x), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - w),
      sq_nonneg (w - y), sq_nonneg (x - z), sq_nonneg (w + y - x - z),
      mul_pos hw hx, mul_pos hx hy, mul_pos hy hz, mul_pos hz hw,
      mul_nonneg hw.le (sq_nonneg (w - z)), mul_nonneg hx.le (sq_nonneg (x - w)),
      mul_nonneg hy.le (sq_nonneg (y - x)), mul_nonneg hz.le (sq_nonneg (z - y)),
      mul_nonneg hz.le (sq_nonneg (w - z)), mul_nonneg hw.le (sq_nonneg (x - w)),
      mul_nonneg hx.le (sq_nonneg (y - x)), mul_nonneg hy.le (sq_nonneg (z - y))]
  have hfin : w * z^2 + x * w^2 + y * x^2 + z * y^2 ≤ 2*t*S - t^2*T := by
    have e2 : 2*t*S - t^2*T = t * S := by
      have : t^2*T = t * (t * T) := by ring
      rw [this, htT]; ring
    rw [e2, htdef, div_mul_eq_mul_div, le_div_iff₀ hT]
    nlinarith [hpoly]
  linarith [hsum, hfin]
