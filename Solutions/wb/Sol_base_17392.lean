import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

/-- Tangent-line trick: `N/D ≥ 2N/t - N*D/t²`, since the difference is `N(t-D)²/(D t²)`. -/
private lemma tang (N D t : ℝ) (hN : 0 ≤ N) (hD : 0 < D) (ht : 0 < t) :
    2 * N / t - N * D / t ^ 2 ≤ N / D := by
  rw [← sub_nonneg]
  have hDne : D ≠ 0 := ne_of_gt hD
  have htne : t ≠ 0 := ne_of_gt ht
  have e : N / D - (2 * N / t - N * D / t ^ 2) = N * (t - D) ^ 2 / (D * t ^ 2) := by
    field_simp
    ring
  rw [e]
  positivity

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * d)
      + (b ^ 2 + c ^ 2 + d ^ 2) / (b * c + c * d + d * a)
      + (a ^ 2 + c ^ 2 + d ^ 2) / (a * b + a * d + c * d)
      + (a ^ 2 + b ^ 2 + d ^ 2) / (a * b + a * d + b * c) ≥ 4 := by
  have hQ : (0:ℝ) < a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by positivity
  have hQne : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≠ 0 := ne_of_gt hQ
  have ht : (0:ℝ) < 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4 := by linarith
  have h1 := tang (a ^ 2 + b ^ 2 + c ^ 2) (a * b + b * c + c * d)
    (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) (by positivity) (by positivity) ht
  have h2 := tang (b ^ 2 + c ^ 2 + d ^ 2) (b * c + c * d + d * a)
    (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) (by positivity) (by positivity) ht
  have h3 := tang (a ^ 2 + c ^ 2 + d ^ 2) (a * b + a * d + c * d)
    (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) (by positivity) (by positivity) ht
  have h4 := tang (a ^ 2 + b ^ 2 + d ^ 2) (a * b + a * d + b * c)
    (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) (by positivity) (by positivity) ht
  -- the polynomial core: 4 * Σ Nᵢ Dᵢ ≤ 9 Q²
  have hE : 4 * ((a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * d)
        + (b ^ 2 + c ^ 2 + d ^ 2) * (b * c + c * d + d * a)
        + (a ^ 2 + c ^ 2 + d ^ 2) * (a * b + a * d + c * d)
        + (a ^ 2 + b ^ 2 + d ^ 2) * (a * b + a * d + b * c))
      ≤ 9 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - a),
      sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a + b + c + d), sq_nonneg (a - b + c - d),
      sq_nonneg (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 - a * b - b * c - c * d - d * a),
      sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - d ^ 2),
      sq_nonneg (d ^ 2 - a ^ 2), sq_nonneg (a ^ 2 + c ^ 2 - b ^ 2 - d ^ 2),
      sq_nonneg (a * b - c * d), sq_nonneg (b * c - d * a),
      sq_nonneg (a ^ 2 - 2 * a * b + b * c),
      sq_nonneg (a * a + b * b + c * c + d * d - 2 * a * b - 2 * c * d)]
  have hcomb : (4:ℝ) ≤
      (2 * (a ^ 2 + b ^ 2 + c ^ 2) / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)
          - (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * d)
            / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ^ 2)
      + (2 * (b ^ 2 + c ^ 2 + d ^ 2) / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)
          - (b ^ 2 + c ^ 2 + d ^ 2) * (b * c + c * d + d * a)
            / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ^ 2)
      + (2 * (a ^ 2 + c ^ 2 + d ^ 2) / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)
          - (a ^ 2 + c ^ 2 + d ^ 2) * (a * b + a * d + c * d)
            / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ^ 2)
      + (2 * (a ^ 2 + b ^ 2 + d ^ 2) / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)
          - (a ^ 2 + b ^ 2 + d ^ 2) * (a * b + a * d + b * c)
            / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ^ 2) := by
    rw [← sub_nonneg]
    have e : (2 * (a ^ 2 + b ^ 2 + c ^ 2) / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)
          - (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * d)
            / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ^ 2)
      + (2 * (b ^ 2 + c ^ 2 + d ^ 2) / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)
          - (b ^ 2 + c ^ 2 + d ^ 2) * (b * c + c * d + d * a)
            / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ^ 2)
      + (2 * (a ^ 2 + c ^ 2 + d ^ 2) / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)
          - (a ^ 2 + c ^ 2 + d ^ 2) * (a * b + a * d + c * d)
            / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ^ 2)
      + (2 * (a ^ 2 + b ^ 2 + d ^ 2) / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)
          - (a ^ 2 + b ^ 2 + d ^ 2) * (a * b + a * d + b * c)
            / (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ^ 2) - 4
        = 4 * (9 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2
              - 4 * ((a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * d)
                + (b ^ 2 + c ^ 2 + d ^ 2) * (b * c + c * d + d * a)
                + (a ^ 2 + c ^ 2 + d ^ 2) * (a * b + a * d + c * d)
                + (a ^ 2 + b ^ 2 + d ^ 2) * (a * b + a * d + b * c)))
          / (9 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2) := by
      field_simp
      ring
    rw [e]
    apply div_nonneg _ (by positivity)
    linarith
  linarith
