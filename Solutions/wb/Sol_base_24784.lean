import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

private lemma cube_le (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 4) :
    p ^ 3 * q ≤ 32 := by
  have hq4 : q = 4 - p := by linarith
  subst hq4
  have hp4 : p < 4 := by linarith
  have e : 32 - p ^ 3 * (4 - p)
      = (p - 3) ^ 2 * (p ^ 2 + 2 * p + 32 / 9) + (5 / 9) * (p * (6 - p)) := by ring
  nlinarith [mul_nonneg (sq_nonneg (p - 3)) (show (0:ℝ) ≤ p ^ 2 + 2 * p + 32 / 9 by positivity),
    mul_pos hp (show (0:ℝ) < 6 - p by linarith), e]

private lemma key (p q X Y : ℝ) (hp : 0 < p) (hq : 0 < q) (hX : 0 < X) (hY : 0 < Y)
    (hXA : 4 * X ≤ p ^ 2) (hYB : 4 * Y ≤ q ^ 2) (hpq : p + q = 4) :
    X * Y * (p ^ 2 + q ^ 2 - 2 * X - 2 * Y) ≤ p * q := by
  have hpq0 : 0 < p * q := mul_pos hp hq
  have h1 : p ^ 3 * q ≤ 32 := cube_le p q hp hq hpq
  have h2 : p * q ^ 3 ≤ 32 := by
    have h := cube_le q p hq hp (by linarith)
    nlinarith [h]
  have hXle : X ≤ p ^ 2 / 4 := by linarith
  have hYle : Y ≤ q ^ 2 / 4 := by linarith
  -- bracket 1 : p*q ≥ 2 * X * Y * (p^2/4)
  have hb1 : 2 * X * Y * (p ^ 2 / 4) ≤ p * q := by
    have hstep : X * Y * (p ^ 2 / 4) ≤ (p ^ 2 / 4) * (q ^ 2 / 4) * (p ^ 2 / 4) := by
      have : X * Y ≤ (p ^ 2 / 4) * (q ^ 2 / 4) :=
        mul_le_mul hXle hYle hY.le (by positivity)
      nlinarith [this, sq_nonneg p]
    have hmul : p ^ 3 * q * (p * q) ≤ 32 * (p * q) :=
      mul_le_mul_of_nonneg_right h1 hpq0.le
    nlinarith [hstep, hmul]
  -- bracket 2 : p*q ≥ 2 * Y * (p^2/4) * (q^2/4)
  have hb2 : 2 * Y * ((p ^ 2 / 4) * (q ^ 2 / 4)) ≤ p * q := by
    have hstep : Y * ((p ^ 2 / 4) * (q ^ 2 / 4)) ≤ (q ^ 2 / 4) * ((p ^ 2 / 4) * (q ^ 2 / 4)) := by
      have hpos : (0:ℝ) ≤ (p ^ 2 / 4) * (q ^ 2 / 4) := by positivity
      exact mul_le_mul_of_nonneg_right hYle hpos
    have hmul : p * q ^ 3 * (p * q) ≤ 32 * (p * q) :=
      mul_le_mul_of_nonneg_right h2 hpq0.le
    nlinarith [hstep, hmul]
  set A : ℝ := p ^ 2 / 4 with hAdef
  set B : ℝ := q ^ 2 / 4 with hBdef
  have hT1 : 0 ≤ (A - X) * (p * q * B - 2 * X * Y * A * B) := by
    have hB0 : 0 ≤ B := by rw [hBdef]; positivity
    apply mul_nonneg (by linarith)
    have : 2 * X * Y * A * B = (2 * X * Y * A) * B := by ring
    rw [this, ← sub_nonneg] at *
    nlinarith [hb1, hB0]
  have hT2 : 0 ≤ (B - Y) * (p * q * X - 2 * X * Y * A * B) := by
    apply mul_nonneg (by linarith)
    have hkey : 2 * Y * (A * B) ≤ p * q := hb2
    nlinarith [hkey, hX]
  have hT3 : 0 ≤ X * Y * (p * q) - X * Y * (A * B) * ((p ^ 2 + q ^ 2) / 2) := by
    have hsum : p ^ 2 + q ^ 2 = 16 - 2 * (p * q) := by nlinarith [hpq]
    have hfac : p * q - (A * B) * ((p ^ 2 + q ^ 2) / 2)
        = p * q * (p * q - 4) ^ 2 / 16 := by
      rw [hAdef, hBdef, hsum]; ring
    have : 0 ≤ p * q - (A * B) * ((p ^ 2 + q ^ 2) / 2) := by
      rw [hfac]; positivity
    nlinarith [this, mul_pos hX hY]
  have hABpos : 0 < A * B := by rw [hAdef, hBdef]; positivity
  have hid : (p * q - X * Y * (p ^ 2 + q ^ 2 - 2 * X - 2 * Y)) * (A * B)
      = (A - X) * (p * q * B - 2 * X * Y * A * B)
        + (B - Y) * (p * q * X - 2 * X * Y * A * B)
        + (X * Y * (p * q) - X * Y * (A * B) * ((p ^ 2 + q ^ 2) / 2)) := by
    rw [hAdef, hBdef]; ring
  nlinarith [hid, hT1, hT2, hT3, hABpos]

theorem solution (a b c d : ℝ) (h : a + b + c + d = 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    1 / (a * b) + 1 / (b * c) + 1 / (c * d) + 1 / (d * a) ≥ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  have hac : (0:ℝ) < a * c := by positivity
  have hbd : (0:ℝ) < b * d := by positivity
  have hk := key (a + c) (b + d) (a * c) (b * d) (by linarith) (by linarith) hac hbd
    (by nlinarith [sq_nonneg (a - c)]) (by nlinarith [sq_nonneg (b - d)]) (by linarith)
  have hexp : (a + c) ^ 2 + (b + d) ^ 2 - 2 * (a * c) - 2 * (b * d)
      = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by ring
  rw [hexp] at hk
  rw [ge_iff_le, ← sub_nonneg]
  have hrw : 1 / (a * b) + 1 / (b * c) + 1 / (c * d) + 1 / (d * a)
      - (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)
      = ((a + c) * (b + d) - a * c * (b * d) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2))
        / (a * b * c * d) := by
    field_simp
    ring
  rw [hrw]
  apply div_nonneg _ (by positivity)
  linarith [hk]
