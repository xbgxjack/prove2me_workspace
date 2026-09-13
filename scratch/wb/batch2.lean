import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

/- [20] base_22008 : Chebyshev termwise,
   3(x³+y³+z³) - (x+y+z)(x²+y²+z²) = Σ (x-y)²(x+y) ≥ 0,
   and each variable lies in exactly three of the four triples. -/
theorem s22008 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a^3 + b^3 + c^3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d)
      + (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b)
      ≥ a^2 + b^2 + c^2 + d^2 := by
  have key : ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z →
      (x^2 + y^2 + z^2)/3 ≤ (x^3 + y^3 + z^3)/(x + y + z) := by
    intro x y z hx hy hz
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith [mul_nonneg (sq_nonneg (x - y)) (by linarith : (0:ℝ) ≤ x + y),
      mul_nonneg (sq_nonneg (y - z)) (by linarith : (0:ℝ) ≤ y + z),
      mul_nonneg (sq_nonneg (z - x)) (by linarith : (0:ℝ) ≤ z + x)]
  have h1 := key a b c ha hb hc
  have h2 := key b c d hb hc hd
  have h3 := key c d a hc hd ha
  have h4 := key d a b hd ha hb
  linarith

/- [10] base_16519 : Cauchy termwise.  Clearing denominators,
   (k u + v + w)(k/u + 1/v + 1/w) - (k+2)² = k w(u-v)² + k v(u-w)² + u(v-w)², all over uvw. -/
theorem s16519 (x y z k : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hk : 0 < k) :
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

/-- AM-GM for three positive reals with product at least one. -/
theorem amgm3 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : 1 ≤ x*y*z) :
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

/- [19] base_44304 : the product of the three fractions is at least one, since
   (d+a²)(d+b²)(d+c²) - (d+bc)(d+ca)(d+ab)
     = d²·½Σ(a-b)² + d·½Σ(ab-bc)² ≥ 0; then apply AM-GM. -/
theorem s44304 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
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
