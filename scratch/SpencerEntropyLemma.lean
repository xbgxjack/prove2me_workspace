import Mathlib

open Finset

/-! Rothvoss Lemma 9 analog: the quantized row-sum of a uniform random ±1 coloring
has bounded Shannon entropy. This is the key new lemma for the joint-entropy route
to Spencer's theorem (see scratch/SPENCER_PLAN.md). -/

noncomputable section

variable {m : ℕ}

/-- The `j`-th coordinate's Rademacher (±1) value under a Boolean coloring. -/
def RSign (χ : Fin m → Bool) (j : Fin m) : ℝ := if χ j then 1 else -1

/-- The signed row sum for a 0/1 row vector `a` under coloring `χ`. -/
def rowSumB (a : Fin m → ℝ) (χ : Fin m → Bool) : ℝ := ∑ j, a j * RSign χ j

lemma abs_rowSumB_le (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1) (χ : Fin m → Bool) :
    |rowSumB a χ| ≤ m := by
  unfold rowSumB
  calc |∑ j, a j * RSign χ j| ≤ ∑ j, |a j * RSign χ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin m, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        have ha : |a j| ≤ 1 := by rcases h01 j with h | h <;> rw [h] <;> norm_num
        have hs : |RSign χ j| = 1 := by unfold RSign; split <;> norm_num
        rw [hs, mul_one]
        exact ha
    _ = m := by simp

-- The quantization threshold width.
variable (Δ : ℝ)

/-- The quantized (shell-index) row sum: which width-`2Δ` interval `rowSumB a χ`
falls into. -/
def shellIdx (a : Fin m → ℝ) (χ : Fin m → Bool) : ℤ := ⌊rowSumB a χ / (2*Δ)⌋

lemma shellIdx_bound (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1) (hΔ : 0 < Δ)
    (χ : Fin m → Bool) :
    (shellIdx Δ a χ : ℝ) ∈ Set.Icc (-((m:ℝ)/(2*Δ) + 1)) ((m:ℝ)/(2*Δ) + 1) := by
  have hb := abs_rowSumB_le a h01 χ
  have hb2 : |rowSumB a χ / (2*Δ)| ≤ (m:ℝ)/(2*Δ) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*Δ)]
    apply div_le_div_of_nonneg_right hb (by positivity)
  rw [abs_le] at hb2
  unfold shellIdx
  have hfl := Int.floor_le (rowSumB a χ / (2*Δ))
  have hfu := Int.lt_floor_add_one (rowSumB a χ / (2*Δ))
  constructor <;> [linarith; linarith]

end
