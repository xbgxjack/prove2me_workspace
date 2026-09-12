import Definitions.Def_DiscreteEntropy
import Mathlib

open Finset

noncomputable section

variable {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] [Nonempty Ω]

private lemma exists_max_empiricalProb (Z : Ω → β) [Nonempty β] :
    ∃ b : β, ∀ b' : β, empiricalProb Z b' ≤ empiricalProb Z b := by
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image (univ : Finset β) (empiricalProb Z) univ_nonempty
  exact ⟨b, fun b' => hb b' (mem_univ b')⟩

private lemma shannonEntropy_ge_neg_logb_max (Z : Ω → β) [Nonempty β] (b : β)
    (hb : ∀ b' : β, empiricalProb Z b' ≤ empiricalProb Z b) (hbpos : 0 < empiricalProb Z b) :
    -Real.logb 2 (empiricalProb Z b) ≤ shannonEntropy Z := by
  unfold shannonEntropy
  have hsplit : ∑ b' : β, (fun p => if p = 0 then 0 else p * Real.logb 2 (1/p)) (empiricalProb Z b')
      = ∑ b' ∈ univ.filter (fun b' => empiricalProb Z b' ≠ 0),
          (empiricalProb Z b') * Real.logb 2 (1/(empiricalProb Z b')) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun b' => empiricalProb Z b' ≠ 0)]
    have hz : ∑ b' ∈ univ.filter (fun b' => ¬ empiricalProb Z b' ≠ 0),
        (fun p => if p = 0 then 0 else p * Real.logb 2 (1/p)) (empiricalProb Z b') = 0 := by
      apply Finset.sum_eq_zero
      intro b' hb'
      simp only [Finset.mem_filter, not_not] at hb'
      simp [hb'.2]
    rw [hz, add_zero]
    apply Finset.sum_congr rfl
    intro b' hb'
    simp only [Finset.mem_filter] at hb'
    simp [hb'.2]
  rw [hsplit]
  have hterm : ∀ b' ∈ univ.filter (fun b' => empiricalProb Z b' ≠ 0),
      (empiricalProb Z b') * Real.logb 2 (1/(empiricalProb Z b))
        ≤ (empiricalProb Z b') * Real.logb 2 (1/(empiricalProb Z b')) := by
    intro b' hb'
    simp only [Finset.mem_filter] at hb'
    have hb'pos : 0 < empiricalProb Z b' :=
      lt_of_le_of_ne (empiricalProb_nonneg Z b') (Ne.symm hb'.2)
    have hmono : Real.logb 2 (1/(empiricalProb Z b)) ≤ Real.logb 2 (1/(empiricalProb Z b')) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity)
        (div_le_div_of_nonneg_left (by norm_num) hb'pos (hb b'))
    exact mul_le_mul_of_nonneg_left hmono (empiricalProb_nonneg Z b')
  calc -Real.logb 2 (empiricalProb Z b)
      = ∑ b' ∈ univ.filter (fun b' => empiricalProb Z b' ≠ 0),
          (empiricalProb Z b') * Real.logb 2 (1/(empiricalProb Z b)) := by
        rw [← Finset.sum_mul, show (∑ b' ∈ univ.filter (fun b' => empiricalProb Z b' ≠ 0),
          empiricalProb Z b') = 1 from ?_]
        · rw [one_mul, Real.logb_div (by norm_num) (by positivity), Real.logb_one]
          ring
        · have h1 := sum_empiricalProb Z (Ω := Ω)
          rw [← Finset.sum_filter_add_sum_filter_not univ (fun b' => empiricalProb Z b' ≠ 0)] at h1
          have hz : ∑ b' ∈ univ.filter (fun b' => ¬ empiricalProb Z b' ≠ 0), empiricalProb Z b' = 0 := by
            apply Finset.sum_eq_zero
            intro b' hb'
            simp only [Finset.mem_filter, not_not] at hb'
            exact hb'.2
          rw [hz, add_zero] at h1
          exact h1
    _ ≤ ∑ b' ∈ univ.filter (fun b' => empiricalProb Z b' ≠ 0),
          (empiricalProb Z b') * Real.logb 2 (1/(empiricalProb Z b')) :=
        Finset.sum_le_sum hterm

end

open Finset in
theorem solution {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] [Nonempty Ω]
    (Z : Ω → β) [Nonempty β] :
    ∃ b : β, (Fintype.card Ω : ℝ) * (2:ℝ) ^ (-shannonEntropy Z)
        ≤ ((univ.filter (fun ω => Z ω = b)).card : ℝ) := by
  obtain ⟨b, hb⟩ := exists_max_empiricalProb (Z := Z)
  have hbpos : 0 < empiricalProb Z b := by
    by_contra hcon
    push_neg at hcon
    have hb0 : empiricalProb Z b = 0 := le_antisymm hcon (empiricalProb_nonneg Z b)
    have hall0 : ∀ b' : β, empiricalProb Z b' = 0 := by
      intro b'
      have := hb b'
      rw [hb0] at this
      exact le_antisymm this (empiricalProb_nonneg Z b')
    have hsum := sum_empiricalProb Z (Ω := Ω)
    simp only [hall0, Finset.sum_const_zero] at hsum
    norm_num at hsum
  refine ⟨b, ?_⟩
  have hge := shannonEntropy_ge_neg_logb_max Z b hb hbpos
  have h2 : (2:ℝ)^(-shannonEntropy Z) ≤ (2:ℝ)^(Real.logb 2 (empiricalProb Z b)) := by
    apply Real.rpow_le_rpow_left_iff (x := (2:ℝ)) (by norm_num) |>.mpr
    linarith
  have h3 : (2:ℝ)^(Real.logb 2 (empiricalProb Z b)) = empiricalProb Z b := by
    rw [Real.rpow_logb (by norm_num) (by norm_num) hbpos]
  rw [h3] at h2
  unfold empiricalProb at h2
  have hcard : (0:ℝ) < (Fintype.card Ω : ℝ) := by
    have := Fintype.card_pos (α := Ω); positivity
  calc (Fintype.card Ω : ℝ) * (2:ℝ)^(-shannonEntropy Z)
      ≤ (Fintype.card Ω : ℝ) * (((univ.filter (fun ω => Z ω = b)).card : ℝ) / (Fintype.card Ω : ℝ)) := by
        apply mul_le_mul_of_nonneg_left h2 (le_of_lt hcard)
    _ = (univ.filter (fun ω => Z ω = b)).card := by
        field_simp
