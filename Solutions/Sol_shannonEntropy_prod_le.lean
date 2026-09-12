import Definitions.Def_DiscreteEntropy
import Theorems.Thm_gibbs_inequality
import Mathlib

open Finset

noncomputable section

variable {Ω β1 β2 : Type*} [Fintype Ω] [Fintype β1] [Fintype β2]
  [DecidableEq β1] [DecidableEq β2] [Nonempty Ω]

private lemma marginal1_eq (Z1 : Ω → β1) (Z2 : Ω → β2) (a : β1) :
    ∑ b : β2, empiricalProb (fun ω => (Z1 ω, Z2 ω)) (a, b) = empiricalProb Z1 a := by
  unfold empiricalProb
  rw [← Finset.sum_div]
  congr 1
  have h1 : (univ.filter (fun ω => Z1 ω = a)).card
      = ∑ b : β2, ((univ.filter (fun ω => Z1 ω = a)).filter (fun ω => Z2 ω = b)).card :=
    Finset.card_eq_sum_card_fiberwise (fun ω _ => mem_univ (Z2 ω))
  rw [h1]
  push_cast
  apply Finset.sum_congr rfl
  intro b _
  congr 2
  ext ω
  simp only [Finset.mem_filter, mem_univ, true_and, Prod.mk.injEq]

private lemma marginal2_eq (Z1 : Ω → β1) (Z2 : Ω → β2) (b : β2) :
    ∑ a : β1, empiricalProb (fun ω => (Z1 ω, Z2 ω)) (a, b) = empiricalProb Z2 b := by
  unfold empiricalProb
  rw [← Finset.sum_div]
  congr 1
  have h1 : (univ.filter (fun ω => Z2 ω = b)).card
      = ∑ a : β1, ((univ.filter (fun ω => Z2 ω = b)).filter (fun ω => Z1 ω = a)).card :=
    Finset.card_eq_sum_card_fiberwise (fun ω _ => mem_univ (Z1 ω))
  rw [h1]
  push_cast
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  ext ω
  simp only [Finset.mem_filter, mem_univ, true_and, Prod.mk.injEq]
  tauto

end

open Finset in
theorem solution {Ω β1 β2 : Type*} [Fintype Ω] [Fintype β1] [Fintype β2]
    [DecidableEq β1] [DecidableEq β2] [Nonempty Ω]
    (Z1 : Ω → β1) (Z2 : Ω → β2) :
    shannonEntropy (fun ω => (Z1 ω, Z2 ω)) ≤ shannonEntropy Z1 + shannonEntropy Z2 := by
  set P : Ω → β1 × β2 := fun ω => (Z1 ω, Z2 ω) with hP_def
  set p : β1 × β2 → ℝ := empiricalProb P with hp_def
  set q : β1 × β2 → ℝ := fun x => empiricalProb Z1 x.1 * empiricalProb Z2 x.2 with hq_def
  have hpq : ∀ x : β1 × β2, p x ≠ 0 → q x ≠ 0 := by
    rintro ⟨a, b⟩ hpne
    have hcardpos : 0 < (univ.filter (fun ω => P ω = (a, b))).card := by
      rcases Nat.eq_zero_or_pos (univ.filter (fun ω => P ω = (a, b))).card with h0 | h0
      · exfalso; apply hpne
        rw [hp_def]; unfold empiricalProb; rw [h0]; simp
      · exact h0
    obtain ⟨ω0, hω0⟩ := Finset.card_pos.mp hcardpos
    simp only [Finset.mem_filter, hP_def, Prod.mk.injEq] at hω0
    have h1 : empiricalProb Z1 a ≠ 0 := by
      unfold empiricalProb
      have : (univ.filter (fun ω => Z1 ω = a)).Nonempty := ⟨ω0, by simp [hω0.2.1]⟩
      positivity
    have h2 : empiricalProb Z2 b ≠ 0 := by
      unfold empiricalProb
      have : (univ.filter (fun ω => Z2 ω = b)).Nonempty := ⟨ω0, by simp [hω0.2.2]⟩
      positivity
    exact mul_ne_zero h1 h2
  have hqsum : ∑ x : β1 × β2, q x = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [hq_def]
    rw [← Finset.sum_mul_sum]
    rw [sum_empiricalProb Z1, sum_empiricalProb Z2]
    ring
  have hgibbs := gibbs_inequality p q (empiricalProb_nonneg P)
    (fun x => mul_nonneg (empiricalProb_nonneg Z1 x.1) (empiricalProb_nonneg Z2 x.2))
    hpq (sum_empiricalProb P) hqsum
  set S := univ.filter (fun x : β1 × β2 => p x ≠ 0) with hS_def
  have hlogsplit : ∀ x ∈ S, p x * Real.log (q x / p x)
      = p x * Real.log (empiricalProb Z1 x.1) + p x * Real.log (empiricalProb Z2 x.2)
          - p x * Real.log (p x) := by
    intro x hx
    simp only [hS_def, Finset.mem_filter] at hx
    have hpxpos : 0 < p x := lt_of_le_of_ne (empiricalProb_nonneg P x) (Ne.symm hx.2)
    have hqxpos : 0 < q x := lt_of_le_of_ne
      (mul_nonneg (empiricalProb_nonneg Z1 x.1) (empiricalProb_nonneg Z2 x.2))
      (Ne.symm (hpq x hx.2))
    have h1pos : 0 < empiricalProb Z1 x.1 := by
      by_contra hcon
      push_neg at hcon
      have := empiricalProb_nonneg Z1 x.1
      have heq0 : empiricalProb Z1 x.1 = 0 := le_antisymm hcon this
      rw [hq_def] at hqxpos
      simp only [heq0, zero_mul] at hqxpos
      exact absurd hqxpos (lt_irrefl 0)
    have h2pos : 0 < empiricalProb Z2 x.2 := by
      by_contra hcon
      push_neg at hcon
      have := empiricalProb_nonneg Z2 x.2
      have heq0 : empiricalProb Z2 x.2 = 0 := le_antisymm hcon this
      rw [hq_def] at hqxpos
      simp only [heq0, mul_zero] at hqxpos
      exact absurd hqxpos (lt_irrefl 0)
    rw [hq_def]
    simp only
    rw [Real.log_div (by positivity) (ne_of_gt hpxpos), Real.log_mul (ne_of_gt h1pos) (ne_of_gt h2pos)]
    ring
  rw [Finset.sum_congr rfl hlogsplit] at hgibbs
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hgibbs
  have hext : ∀ (f : β1 × β2 → ℝ), (∀ x, p x = 0 → f x = 0) →
      ∑ x ∈ S, f x = ∑ x : β1 × β2, f x := by
    intro f hf
    rw [hS_def]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x _ hx
    simp only [Finset.mem_filter, mem_univ, true_and, not_not] at hx
    exact hf x hx
  have hterm1 : ∑ x ∈ S, p x * Real.log (empiricalProb Z1 x.1)
      = ∑ a : β1, empiricalProb Z1 a * Real.log (empiricalProb Z1 a) := by
    rw [hext (fun x => p x * Real.log (empiricalProb Z1 x.1)) (fun x hx => by rw [hx]; ring)]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    dsimp only
    rw [← Finset.sum_mul, marginal1_eq]
  have hterm2 : ∑ x ∈ S, p x * Real.log (empiricalProb Z2 x.2)
      = ∑ b : β2, empiricalProb Z2 b * Real.log (empiricalProb Z2 b) := by
    rw [hext (fun x => p x * Real.log (empiricalProb Z2 x.2)) (fun x hx => by rw [hx]; ring)]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    dsimp only
    rw [← Finset.sum_mul, marginal2_eq]
  have hterm3 : ∑ x ∈ S, p x * Real.log (p x) = ∑ x : β1 × β2, p x * Real.log (p x) :=
    hext (fun x => p x * Real.log (p x)) (fun x hx => by rw [hx]; ring)
  rw [hterm1, hterm2, hterm3, hp_def] at hgibbs
  have hlog2 : Real.log 2 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  have hconvP : ∑ x : β1 × β2, empiricalProb P x * Real.log (empiricalProb P x)
      = - Real.log 2 * shannonEntropy P := by
    unfold shannonEntropy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : empiricalProb P x = 0
    · simp [hx]
    · simp only [hx, if_false]
      rw [Real.logb, one_div, Real.log_inv]
      field_simp
  have hconvZ1 : ∑ a : β1, empiricalProb Z1 a * Real.log (empiricalProb Z1 a)
      = - Real.log 2 * shannonEntropy Z1 := by
    unfold shannonEntropy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : empiricalProb Z1 a = 0
    · simp [ha]
    · simp only [ha, if_false]
      rw [Real.logb, one_div, Real.log_inv]
      field_simp
  have hconvZ2 : ∑ b : β2, empiricalProb Z2 b * Real.log (empiricalProb Z2 b)
      = - Real.log 2 * shannonEntropy Z2 := by
    unfold shannonEntropy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : empiricalProb Z2 b = 0
    · simp [hb]
    · simp only [hb, if_false]
      rw [Real.logb, one_div, Real.log_inv]
      field_simp
  rw [hconvP, hconvZ1, hconvZ2] at hgibbs
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [hgibbs]
