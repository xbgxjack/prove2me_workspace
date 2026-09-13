import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

private lemma core (P Q s t : ℝ) (hP : 0 < P) (hQ : 0 < Q) (hs0 : 0 < s) (ht0 : 0 < t)
    (hs : 4 * P ≤ s ^ 2) (ht : 4 * Q ≤ t ^ 2) :
    4 * (P ^ 2 + Q ^ 2) * (P * Q) ≤ s * t * (P ^ 2 * (s ^ 2 - 3 * P) + Q ^ 2 * (t ^ 2 - 3 * Q)) := by
  have hst : 0 < s * t := mul_pos hs0 ht0
  -- drop to the cube bound
  have hdrop : P ^ 3 + Q ^ 3 ≤ P ^ 2 * (s ^ 2 - 3 * P) + Q ^ 2 * (t ^ 2 - 3 * Q) := by
    nlinarith [sq_nonneg P, sq_nonneg Q, hs, ht, hP.le, hQ.le, mul_pos hP hP, mul_pos hQ hQ]
  have hcube : 0 < P ^ 3 + Q ^ 3 := by positivity
  -- the squared inequality
  have hsq : (4 * (P ^ 2 + Q ^ 2) * (P * Q)) ^ 2 ≤ (s * t * (P ^ 3 + Q ^ 3)) ^ 2 := by
    have h16 : 16 * (P * Q) ≤ (s * t) ^ 2 := by
      nlinarith [hs, ht, hP.le, hQ.le, sq_nonneg s, sq_nonneg t]
    have hfac : (P ^ 3 + Q ^ 3) ^ 2 - (P * Q) * (P ^ 2 + Q ^ 2) ^ 2
        = (P - Q) ^ 2 * (P ^ 4 + P ^ 3 * Q + P ^ 2 * Q ^ 2 + P * Q ^ 3 + Q ^ 4) := by ring
    have hPQ2 : (P * Q) * (P ^ 2 + Q ^ 2) ^ 2 ≤ (P ^ 3 + Q ^ 3) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (P - Q))
        (show (0:ℝ) ≤ P ^ 4 + P ^ 3 * Q + P ^ 2 * Q ^ 2 + P * Q ^ 3 + Q ^ 4 by positivity), hfac]
    have hA : 0 ≤ (P ^ 3 + Q ^ 3) ^ 2 := sq_nonneg _
    calc (4 * (P ^ 2 + Q ^ 2) * (P * Q)) ^ 2
        = 16 * (P * Q) * ((P * Q) * (P ^ 2 + Q ^ 2) ^ 2) := by ring
      _ ≤ 16 * (P * Q) * (P ^ 3 + Q ^ 3) ^ 2 := by
          apply mul_le_mul_of_nonneg_left hPQ2 (by positivity)
      _ ≤ (s * t) ^ 2 * (P ^ 3 + Q ^ 3) ^ 2 :=
          mul_le_mul_of_nonneg_right h16 hA
      _ = (s * t * (P ^ 3 + Q ^ 3)) ^ 2 := by ring
  have hU : 0 ≤ s * t * (P ^ 3 + Q ^ 3) := by positivity
  have hV : 0 ≤ 4 * (P ^ 2 + Q ^ 2) * (P * Q) := by positivity
  have hstep : 4 * (P ^ 2 + Q ^ 2) * (P * Q) ≤ s * t * (P ^ 3 + Q ^ 3) := by
    nlinarith [hsq, hU, hV]
  have hmono : s * t * (P ^ 3 + Q ^ 3)
      ≤ s * t * (P ^ 2 * (s ^ 2 - 3 * P) + Q ^ 2 * (t ^ 2 - 3 * Q)) :=
    mul_le_mul_of_nonneg_left hdrop hst.le
  linarith

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a ^ 4 * c ^ 2 + b ^ 4 * d ^ 2) / (c * d) + (b ^ 4 * d ^ 2 + c ^ 4 * a ^ 2) / (d * a)
      + (c ^ 4 * a ^ 2 + d ^ 4 * b ^ 2) / (a * b) + (d ^ 4 * b ^ 2 + a ^ 4 * c ^ 2) / (b * c)
      ≥ 4 * (a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2) := by
  have hP : (0:ℝ) < a * c := by positivity
  have hQ : (0:ℝ) < b * d := by positivity
  have hk := core (a * c) (b * d) (a + c) (b + d) hP hQ (by linarith) (by linarith)
    (by nlinarith [sq_nonneg (a - c)]) (by nlinarith [sq_nonneg (b - d)])
  rw [ge_iff_le, ← sub_nonneg]
  have hrw : (a ^ 4 * c ^ 2 + b ^ 4 * d ^ 2) / (c * d) + (b ^ 4 * d ^ 2 + c ^ 4 * a ^ 2) / (d * a)
      + (c ^ 4 * a ^ 2 + d ^ 4 * b ^ 2) / (a * b) + (d ^ 4 * b ^ 2 + a ^ 4 * c ^ 2) / (b * c)
      - 4 * (a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2)
      = ((a + c) * (b + d) * ((a * c) ^ 2 * ((a + c) ^ 2 - 3 * (a * c))
            + (b * d) ^ 2 * ((b + d) ^ 2 - 3 * (b * d)))
          - 4 * ((a * c) ^ 2 + (b * d) ^ 2) * ((a * c) * (b * d)))
        / ((a * c) * (b * d)) := by
    field_simp
    ring
  rw [hrw]
  apply div_nonneg _ (by positivity)
  linarith
