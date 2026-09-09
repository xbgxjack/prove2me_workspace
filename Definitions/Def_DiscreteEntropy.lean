import Mathlib

open Finset

noncomputable section

variable {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]

/-- The empirical probability that `Z : Ω → β` takes the value `b`, under the uniform
distribution on the finite sample space `Ω`. -/
def empiricalProb (Z : Ω → β) (b : β) : ℝ :=
  ((univ.filter (fun ω => Z ω = b)).card : ℝ) / (Fintype.card Ω : ℝ)

/-- The base-2 Shannon entropy of `Z : Ω → β`, computed from its empirical distribution under
the uniform measure on `Ω`, following the usual convention that a zero-probability outcome
contributes `0` to the sum (since `p log(1/p) → 0` as `p → 0⁺`). -/
def shannonEntropy (Z : Ω → β) : ℝ :=
  ∑ b : β, (fun p => if p = 0 then 0 else p * Real.logb 2 (1 / p)) (empiricalProb Z b)

lemma empiricalProb_nonneg (Z : Ω → β) (b : β) : 0 ≤ empiricalProb Z b := by
  unfold empiricalProb
  positivity

lemma sum_empiricalProb (Z : Ω → β) [Nonempty Ω] :
    ∑ b : β, empiricalProb Z b = 1 := by
  unfold empiricalProb
  rw [← Finset.sum_div]
  have hsum : ∑ b : β, ((univ.filter (fun ω => Z ω = b)).card : ℝ) = (Fintype.card Ω : ℝ) := by
    have h1 : (univ : Finset Ω).card
        = ∑ b ∈ (univ : Finset β), (univ.filter (fun ω => Z ω = b)).card :=
      Finset.card_eq_sum_card_fiberwise (fun a _ => mem_univ _)
    rw [Fintype.card]
    exact_mod_cast h1.symm
  rw [hsum]
  have hne : (Fintype.card Ω : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := Ω)
    positivity
  field_simp

end
