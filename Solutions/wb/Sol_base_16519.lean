import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

theorem solution (x y z k : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hk : 0 < k) :
    1 / (k * x + y + z) + 1 / (x + k * y + z) + 1 / (x + y + k * z)
      ≤ 1 / (k + 2) * (1 / x + 1 / y + 1 / z) := by
  have key : ∀ u v w : ℝ, 0 < u → 0 < v → 0 < w →
      1 / (k * u + v + w) ≤ (k/u + 1/v + 1/w) / (k + 2)^2 := by
    intro u v w hu hv hw
    have hden : 0 < k * u + v + w := by positivity
    have hpoly : (k + 2)^2 * (u*v*w) ≤ (k*(v*w) + u*w + u*v) * (k*u + v + w) := by
      nlinarith [mul_nonneg (mul_nonneg hk.le hw.le) (sq_nonneg (u - v)),
        mul_nonneg (mul_nonneg hk.le hv.le) (sq_nonneg (u - w)),
        mul_nonneg hu.le (sq_nonneg (v - w))]
    rw [div_le_div_iff₀ hden (by positivity)]
    have he : k/u + 1/v + 1/w = (k*(v*w) + u*w + u*v) / (u*v*w) := by
      field_simp
    rw [he, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [hpoly]
  have h1 := key x y z hx hy hz
  have h2 := key y x z hy hx hz
  have h3 := key z x y hz hx hy
  have e2 : x + k * y + z = k * y + x + z := by ring
  have e3 : x + y + k * z = k * z + x + y := by ring
  rw [e2, e3]
  have hsum : (k/x + 1/y + 1/z) / (k + 2)^2 + (k/y + 1/x + 1/z) / (k + 2)^2
      + (k/z + 1/x + 1/y) / (k + 2)^2 = 1 / (k + 2) * (1 / x + 1 / y + 1 / z) := by
    field_simp; ring
  linarith [h1, h2, h3, hsum.ge, hsum.le]
