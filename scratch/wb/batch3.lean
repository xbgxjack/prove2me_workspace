import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

/- [5] base_33327 : a+b+c = 3 ⊢ a¹²+b¹²+c¹²+8(ab+bc+ca) ≥ 27.
   Since (a+b+c)² = 9 gives Σa² = 9 - 2q, the claim is Σa¹² ≥ 4Σa² - 9, which is
   the tangent-line bound Σ h(aᵢ) ≥ 0 for h(t) = t¹² - 4t² - 4t + 7.  And
   h(t) = (t-1)²(t¹⁰+2t⁹+3t⁸+4t⁷+5t⁶+6t⁵+7t⁴+8t³+9t²+10t+7), all coefficients positive. -/
theorem s33327 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) :
    a ^ 12 + b ^ 12 + c ^ 12 + 8 * (a * b + b * c + c * a) ≥ 27 := by
  have key : ∀ t : ℝ, 0 ≤ t → 0 ≤ t^12 - 4*t^2 - 4*t + 7 := by
    intro t ht
    have e : t^12 - 4*t^2 - 4*t + 7
        = (t-1)^2 * (t^10 + 2*t^9 + 3*t^8 + 4*t^7 + 5*t^6 + 6*t^5 + 7*t^4 + 8*t^3
            + 9*t^2 + 10*t + 7) := by ring
    rw [e]
    have hpos : (0:ℝ) ≤ t^10 + 2*t^9 + 3*t^8 + 4*t^7 + 5*t^6 + 6*t^5 + 7*t^4 + 8*t^3
        + 9*t^2 + 10*t + 7 := by positivity
    exact mul_nonneg (sq_nonneg _) hpos
  have hsq : a^2 + b^2 + c^2 + 2*(a*b + b*c + c*a) = 9 := by
    linear_combination (a + b + c + 3) * hab
  linarith [key a ha.le, key b hb.le, key c hc.le, hsq, hab]

/- [6] base_41666 : with the cycle w→z→y→x→w the claim is Σ aᵢ⁴/aᵢ₊₁ ≥ Σ aᵢaᵢ₊₁².
   Cauchy in Engel form: a⁴/b ≥ 2a²t - t²b for every t, since the difference is
   (a²-tb)²/b.  Taking t = S/T with S = Σaᵢ², T = Σaᵢ sums to S²/T, and it remains
   to check the polynomial inequality S² ≥ T·(Σ aᵢaᵢ₊₁²). -/
theorem s41666 (w x y z : ℝ) (hw : 0 < w) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (w^4 / z + x^4 / w + y^4 / x + z^4 / y) ≥ w * z^2 + x * w^2 + y * x^2 + z * y^2 := by
  have hT : (0:ℝ) < w + x + y + z := by linarith
  set S : ℝ := w^2 + x^2 + y^2 + z^2 with hS
  set T : ℝ := w + x + y + z with hTdef
  set t : ℝ := S / T with htdef
  have htT : t * T = S := by field_simp [htdef]
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
