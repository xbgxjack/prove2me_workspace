import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

/-- The polynomial core: `G H p q ≤ G q² M + H p² K` whenever `G ≤ p²`, `H ≤ q²`
and `p q ≤ M + K`, all quantities nonnegative. -/
private lemma core (G H p q M K : ℝ) (hG0 : 0 ≤ G) (hH0 : 0 ≤ H) (hp : 0 < p) (hq : 0 < q)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hG : G ≤ p ^ 2) (hH : H ≤ q ^ 2) (hMK : p * q ≤ M + K) :
    G * H * (p * q) ≤ G * q ^ 2 * M + H * p ^ 2 * K := by
  rcases le_total (G * q ^ 2) (H * p ^ 2) with hc | hc
  · have ha : 0 ≤ G * q ^ 2 * (M + K - p * q) := by
      apply mul_nonneg (by positivity); linarith
    have hb : 0 ≤ K * (H * p ^ 2 - G * q ^ 2) := mul_nonneg hK (by linarith)
    have hcc : 0 ≤ G * (p * q) * (q ^ 2 - H) := by
      apply mul_nonneg (by positivity); linarith
    nlinarith [ha, hb, hcc]
  · have ha : 0 ≤ H * p ^ 2 * (M + K - p * q) := by
      apply mul_nonneg (by positivity); linarith
    have hb : 0 ≤ M * (G * q ^ 2 - H * p ^ 2) := mul_nonneg hM (by linarith)
    have hcc : 0 ≤ H * (p * q) * (p ^ 2 - G) := by
      apply mul_nonneg (by positivity); linarith
    nlinarith [ha, hb, hcc]

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a - b) * (a - c) / (a + b) / (a + c) + (-c + b) * (-d + b) / (b + c) / (b + d)
      + (-d + c) * (-a + c) / (c + d) / (a + c) + (d - a) * (-b + d) / (a + d) / (b + d) ≥ 0 := by
  have hkey := core ((a - c) ^ 2) ((b - d) ^ 2) (a + c) (b + d) ((a + d) * (b + c))
    ((a + b) * (c + d)) (sq_nonneg _) (sq_nonneg _) (by linarith) (by linarith)
    (by positivity) (by positivity) (by nlinarith [mul_pos ha hc]) (by nlinarith [mul_pos hb hd])
    (by nlinarith [mul_pos ha hc, mul_pos hb hd])
  rw [ge_iff_le, ← sub_nonneg]
  have hrw : (a - b) * (a - c) / (a + b) / (a + c) + (-c + b) * (-d + b) / (b + c) / (b + d)
      + (-d + c) * (-a + c) / (c + d) / (a + c) + (d - a) * (-b + d) / (a + d) / (b + d) - 0
      = ((a - c) ^ 2 * (b + d) ^ 2 * ((a + d) * (b + c))
          + (b - d) ^ 2 * (a + c) ^ 2 * ((a + b) * (c + d))
          - (a - c) ^ 2 * (b - d) ^ 2 * ((a + c) * (b + d)))
        / ((a + c) * (b + d) * (a + b) * (b + c) * (c + d) * (d + a)) := by
    field_simp
    ring
  rw [hrw]
  apply div_nonneg _ (by positivity)
  linarith
