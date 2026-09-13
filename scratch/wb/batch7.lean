import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

/-- Two-term Engel form (Cauchy–Schwarz). -/
private lemma engel2 (x y z w : ℝ) (hy : 0 < y) (hw : 0 < w) :
    (x + z) ^ 2 / (y + w) ≤ x ^ 2 / y + z ^ 2 / w := by
  rw [div_add_div _ _ (ne_of_gt hy) (ne_of_gt hw),
    div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith [sq_nonneg (x * w - z * y), mul_pos hy hw, hy, hw]

theorem s31243 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (b * (-d + 2 * b - c) / (b + c + d) + c * (-d + 2 * c - a) / (c + d + a)
      + d * (2 * d - b - a) / (d + a + b) + a * (2 * a - b - c) / (a + b + c)) ≥ 0 := by
  have p1 : (0:ℝ) < b + c + d := by linarith
  have p2 : (0:ℝ) < c + d + a := by linarith
  have p3 : (0:ℝ) < d + a + b := by linarith
  have p4 : (0:ℝ) < a + b + c := by linarith
  -- rewrite each term as 3 x² / D - x
  have e1 : b * (-d + 2 * b - c) / (b + c + d) = 3 * (b ^ 2 / (b + c + d)) - b := by
    field_simp; ring
  have e2 : c * (-d + 2 * c - a) / (c + d + a) = 3 * (c ^ 2 / (c + d + a)) - c := by
    field_simp; ring
  have e3 : d * (2 * d - b - a) / (d + a + b) = 3 * (d ^ 2 / (d + a + b)) - d := by
    field_simp; ring
  have e4 : a * (2 * a - b - c) / (a + b + c) = 3 * (a ^ 2 / (a + b + c)) - a := by
    field_simp; ring
  rw [e1, e2, e3, e4]
  -- Cauchy–Schwarz in Engel form
  have c12 : (b + c) ^ 2 / ((b + c + d) + (c + d + a))
      ≤ b ^ 2 / (b + c + d) + c ^ 2 / (c + d + a) := engel2 b (b + c + d) c (c + d + a) p1 p2
  have c34 : (d + a) ^ 2 / ((d + a + b) + (a + b + c))
      ≤ d ^ 2 / (d + a + b) + a ^ 2 / (a + b + c) := engel2 d (d + a + b) a (a + b + c) p3 p4
  have call : ((b + c) + (d + a)) ^ 2 / (((b + c + d) + (c + d + a)) + ((d + a + b) + (a + b + c)))
      ≤ (b + c) ^ 2 / ((b + c + d) + (c + d + a)) + (d + a) ^ 2 / ((d + a + b) + (a + b + c)) :=
    engel2 (b + c) ((b + c + d) + (c + d + a)) (d + a) ((d + a + b) + (a + b + c))
      (by linarith) (by linarith)
  have hval : ((b + c) + (d + a)) ^ 2
      / (((b + c + d) + (c + d + a)) + ((d + a + b) + (a + b + c)))
      = (a + b + c + d) / 3 := by
    rw [show ((b + c + d) + (c + d + a)) + ((d + a + b) + (a + b + c)) = 3 * (a + b + c + d) by ring,
      show ((b:ℝ) + c) + (d + a) = a + b + c + d by ring]
    rw [eq_div_iff (by norm_num : (3:ℝ) ≠ 0)]
    field_simp
  rw [hval] at call
  have hsum : (a + b + c + d) / 3
      ≤ b ^ 2 / (b + c + d) + c ^ 2 / (c + d + a) + d ^ 2 / (d + a + b) + a ^ 2 / (a + b + c) := by
    linarith
  linarith
