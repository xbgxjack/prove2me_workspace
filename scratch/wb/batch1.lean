import Mathlib
open Real Nat

-- [6] plus_75566 : (a+3)^2+(b+1)^2+(c+2)^2 ≥ 0 after adding both constraints
theorem s75566 (a b c : ℝ) (ha : a^2 + 2 * b = 7) (hb : b^2 + 4 * c = -7) :
    c^2 + 6 * a ≥ -14 := by
  nlinarith [sq_nonneg (a + 3), sq_nonneg (b + 1), sq_nonneg (c + 2)]

-- [7] plus_50717 : 4*LHS = (2x²+ax)² + (4b-a²-c²)x² + (cx+2)²
theorem s50717 (a b c d x : ℝ) (a2c2_leq_4b : a^2 + c^2 ≤ 4*b) :
    x^4 + a*x^3 + b*x^2 + c*x + 1 ≥ 0 := by
  nlinarith [sq_nonneg (2*x^2 + a*x), sq_nonneg (c*x + 2),
    mul_nonneg (sub_nonneg.2 a2c2_leq_4b) (sq_nonneg x)]

-- [0] base_38006 : 16u² - (v+30)² = 15(v-2)² with u = a²+b², v = ab
theorem s38006 (a b : ℝ) (h : a^4 + b^4 + a^2 * b^2 = 60) :
    4 * a^2 + 4 * b^2 - a * b ≥ 30 := by
  nlinarith [sq_nonneg (a*b - 2), sq_nonneg (a - b), sq_nonneg (a + b),
    sq_nonneg (a^2 + b^2), sq_nonneg (a*b), sq_nonneg (a^2 - b^2)]

-- [12] base_31532
theorem s31532 (a b c : ℝ) (h : a + b + c = -6) :
    a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 12 * a * b * c + 48 ≥ 0 := by
  nlinarith [sq_nonneg (a*b + b*c + c*a - 12), sq_nonneg (a - b), sq_nonneg (b - c),
    sq_nonneg (c - a), sq_nonneg (a + 2), sq_nonneg (b + 2), sq_nonneg (c + 2),
    sq_nonneg (a*b - 4), sq_nonneg (b*c - 4), sq_nonneg (c*a - 4),
    sq_nonneg (a + b + 4), sq_nonneg (a*b + b*c + c*a)]

-- [2] plus_45827 : difference is 3t²+5t³+3t⁴ with t = |a|
theorem s45827 (a : ℝ) : (1 + |a| + a^2)^3 ≥ (1 + |a|)^3 * (1 + |a|^3) := by
  have ht : (0:ℝ) ≤ |a| := abs_nonneg a
  have h2 : a^2 = |a|^2 := (sq_abs a).symm
  rw [h2]
  nlinarith [ht, mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht,
    mul_nonneg (mul_nonneg (mul_nonneg ht ht) ht) ht]

-- [8] base_11560 : equality at (-1,-1,2)
theorem s11560 (a b c : ℝ) (habc : a + b + c = 0) :
    a^2 * b^2 + a^2 * c^2 + b^2 * c^2 + 3 ≥ 6 * a * b * c := by
  nlinarith [sq_nonneg (a*b + b*c + c*a + 3), sq_nonneg (a*b*c - 2),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a),
    sq_nonneg (a*b + b*c + c*a)]

-- [13] base_3816 : equality at (-1,-1,-1)
theorem s3816 (x y z : ℝ) (h : x ^ 4 + y ^ 4 + z ^ 4 = 3) :
    x ^ 2 * (x + y) + y ^ 2 * (y + z) + z ^ 2 * (z + x) ≥ -6 := by
  nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (z + 1),
    sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (z^2 - 1),
    sq_nonneg (x + y), sq_nonneg (y + z), sq_nonneg (z + x),
    sq_nonneg (x^2 + x), sq_nonneg (y^2 + y), sq_nonneg (z^2 + z)]

-- [4] base_8123
theorem s8123 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    (2 * a ^ 2 + 1) * (2 * b ^ 2 + 1) * (2 * c ^ 2 + 1) ≥ 3 * (a + b + c) ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a*b - 1), sq_nonneg (b*c - 1), sq_nonneg (c*a - 1),
    mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb),
    mul_nonneg (sub_nonneg.2 hb) (sub_nonneg.2 hc),
    mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 ha),
    sq_nonneg (a*b*c - 1), sq_nonneg (a + b + c - 3)]
