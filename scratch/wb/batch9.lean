import Mathlib
open Real Nat

set_option maxHeartbeats 1600000

/-- Two-term Engel form (Cauchy–Schwarz). -/
private lemma engel2 (x y z w : ℝ) (hy : 0 < y) (hw : 0 < w) :
    (x + z) ^ 2 / (y + w) ≤ x ^ 2 / y + z ^ 2 / w := by
  rw [div_add_div _ _ (ne_of_gt hy) (ne_of_gt hw),
    div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith [sq_nonneg (x * w - z * y), mul_pos hy hw, hy, hw]

theorem s10465 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) :
    9 / (a * b + b * c + c * a) + (a + b) / (a ^ 2 + a * b + c)
      + (b + c) / (b ^ 2 + b * c + a) + (c + a) / (c ^ 2 + c * a + b) ≥ 5 := by
  have hq : (0:ℝ) < a * b + b * c + c * a := by positivity
  have hD1 : (0:ℝ) < (a + b) * (a ^ 2 + a * b + c) := by positivity
  have hD2 : (0:ℝ) < (b + c) * (b ^ 2 + b * c + a) := by positivity
  have hD3 : (0:ℝ) < (c + a) * (c ^ 2 + c * a + b) := by positivity
  have hT : (0:ℝ) < (a + b) * (a ^ 2 + a * b + c) + (b + c) * (b ^ 2 + b * c + a)
      + (c + a) * (c ^ 2 + c * a + b) := by linarith
  -- each fraction as a square over a product
  have e1 : (a + b) ^ 2 / ((a + b) * (a ^ 2 + a * b + c)) = (a + b) / (a ^ 2 + a * b + c) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have e2 : (b + c) ^ 2 / ((b + c) * (b ^ 2 + b * c + a)) = (b + c) / (b ^ 2 + b * c + a) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have e3 : (c + a) ^ 2 / ((c + a) * (c ^ 2 + c * a + b)) = (c + a) / (c ^ 2 + c * a + b) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  -- Cauchy–Schwarz (Engel form) on the three fractions
  have c12 := engel2 (a + b) ((a + b) * (a ^ 2 + a * b + c)) (b + c)
    ((b + c) * (b ^ 2 + b * c + a)) hD1 hD2
  have c123 := engel2 ((a + b) + (b + c))
    ((a + b) * (a ^ 2 + a * b + c) + (b + c) * (b ^ 2 + b * c + a)) (c + a)
    ((c + a) * (c ^ 2 + c * a + b)) (by linarith) hD3
  have hnum : ((a + b) + (b + c) + (c + a)) ^ 2 = 36 := by
    have h6 : (a + b) + (b + c) + (c + a) = 6 := by linarith
    rw [h6]; norm_num
  rw [show (a + b + (b + c)) + (c + a) = (a + b) + (b + c) + (c + a) by ring, hnum] at c123
  have hEngel : 36 / ((a + b) * (a ^ 2 + a * b + c) + (b + c) * (b ^ 2 + b * c + a)
      + (c + a) * (c ^ 2 + c * a + b))
      ≤ (a + b) / (a ^ 2 + a * b + c) + (b + c) / (b ^ 2 + b * c + a)
        + (c + a) / (c ^ 2 + c * a + b) := by
    rw [← e1, ← e2, ← e3]
    rw [show (a + b) * (a ^ 2 + a * b + c) + (b + c) * (b ^ 2 + b * c + a)
        + (c + a) * (c ^ 2 + c * a + b)
        = ((a + b) * (a ^ 2 + a * b + c) + (b + c) * (b ^ 2 + b * c + a))
          + (c + a) * (c ^ 2 + c * a + b) by ring]
    linarith [c12, c123]
  -- the polynomial heart: 9 T + 36 q - 5 q T ≥ 0
  have hpoly : 0 ≤ 9 * ((a + b) * (a ^ 2 + a * b + c) + (b + c) * (b ^ 2 + b * c + a)
        + (c + a) * (c ^ 2 + c * a + b))
      + 36 * (a * b + b * c + c * a)
      - 5 * (a * b + b * c + c * a) * ((a + b) * (a ^ 2 + a * b + c)
        + (b + c) * (b ^ 2 + b * c + a) + (c + a) * (c ^ 2 + c * a + b)) := by
    have hA1 : a ^ 2 * b + b ^ 2 * c + c ^ 2 * a - 3 ≤ 5 / 2 * (a ^ 2 + b ^ 2 + c ^ 2 - 3) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a + b - 2 * c),
        mul_nonneg ha.le (sq_nonneg (b - c)), mul_nonneg hb.le (sq_nonneg (c - a)),
        mul_nonneg hc.le (sq_nonneg (a - b)), mul_nonneg ha.le (sq_nonneg (a - b)),
        mul_nonneg hb.le (sq_nonneg (b - c)), mul_nonneg hc.le (sq_nonneg (c - a)),
        mul_pos (mul_pos ha hb) hc]
    have hA2 : 3 - (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ≤ 5 / 2 * (a ^ 2 + b ^ 2 + c ^ 2 - 3) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a + b - 2 * c),
        mul_nonneg ha.le (sq_nonneg (b - c)), mul_nonneg hb.le (sq_nonneg (c - a)),
        mul_nonneg hc.le (sq_nonneg (a - b)), mul_nonneg ha.le (sq_nonneg (a - b)),
        mul_nonneg hb.le (sq_nonneg (b - c)), mul_nonneg hc.le (sq_nonneg (c - a)),
        mul_pos (mul_pos ha hb) hc]
    have hD0 : (0:ℝ) ≤ a ^ 2 + b ^ 2 + c ^ 2 - 3 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have hD6 : a ^ 2 + b ^ 2 + c ^ 2 - 3 ≤ 6 := by nlinarith [hq]
    have hid : 2 * (9 * ((a + b) * (a ^ 2 + a * b + c) + (b + c) * (b ^ 2 + b * c + a)
          + (c + a) * (c ^ 2 + c * a + b))
        + 36 * (a * b + b * c + c * a)
        - 5 * (a * b + b * c + c * a) * ((a + b) * (a ^ 2 + a * b + c)
          + (b + c) * (b ^ 2 + b * c + a) + (c + a) * (c ^ 2 + c * a + b)))
        = 10 * (a ^ 2 + b ^ 2 + c ^ 2 - 3) ^ 2 + 30 * (a ^ 2 + b ^ 2 + c ^ 2 - 3)
          + ((a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) - 3) * (5 * (a ^ 2 + b ^ 2 + c ^ 2 - 3) - 12) := by
      have hcc : c = 3 - a - b := by linarith
      subst hcc
      ring
    have p1 : (0:ℝ) ≤ (5 / 2 * (a ^ 2 + b ^ 2 + c ^ 2 - 3) - (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a - 3))
        * (6 - (a ^ 2 + b ^ 2 + c ^ 2 - 3)) := mul_nonneg (by linarith) (by linarith)
    have p2 : (0:ℝ) ≤ (a ^ 2 + b ^ 2 + c ^ 2 - 3)
        * (5 / 2 * (a ^ 2 + b ^ 2 + c ^ 2 - 3) + (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a - 3)) :=
      mul_nonneg hD0 (by linarith)
    nlinarith [hid, p1, p2, sq_nonneg (a ^ 2 + b ^ 2 + c ^ 2 - 3)]
  -- assemble
  have hfin : (5:ℝ) ≤ 9 / (a * b + b * c + c * a)
      + 36 / ((a + b) * (a ^ 2 + a * b + c) + (b + c) * (b ^ 2 + b * c + a)
        + (c + a) * (c ^ 2 + c * a + b)) := by
    rw [← sub_nonneg]
    have hrw : 9 / (a * b + b * c + c * a)
        + 36 / ((a + b) * (a ^ 2 + a * b + c) + (b + c) * (b ^ 2 + b * c + a)
          + (c + a) * (c ^ 2 + c * a + b)) - 5
        = (9 * ((a + b) * (a ^ 2 + a * b + c) + (b + c) * (b ^ 2 + b * c + a)
              + (c + a) * (c ^ 2 + c * a + b))
            + 36 * (a * b + b * c + c * a)
            - 5 * (a * b + b * c + c * a) * ((a + b) * (a ^ 2 + a * b + c)
              + (b + c) * (b ^ 2 + b * c + a) + (c + a) * (c ^ 2 + c * a + b)))
          / ((a * b + b * c + c * a) * ((a + b) * (a ^ 2 + a * b + c)
              + (b + c) * (b ^ 2 + b * c + a) + (c + a) * (c ^ 2 + c * a + b))) := by
      field_simp
    rw [hrw]
    exact div_nonneg hpoly (by positivity)
  linarith [hEngel, hfin]
