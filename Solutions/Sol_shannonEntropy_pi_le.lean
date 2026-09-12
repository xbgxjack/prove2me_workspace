import Definitions.Def_DiscreteEntropy
import Theorems.Thm_shannonEntropy_prod_le
import Mathlib

open Finset

noncomputable section

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

omit [Nonempty Ω] in
private lemma shannonEntropy_comp_equiv {β β' : Type*} [Fintype β] [DecidableEq β]
    [Fintype β'] [DecidableEq β'] (e : β ≃ β') (Z : Ω → β) :
    shannonEntropy (fun ω => e (Z ω)) = shannonEntropy Z := by
  unfold shannonEntropy
  rw [← Equiv.sum_comp e (fun b' => (fun p => if p = 0 then 0 else p * Real.logb 2 (1 / p))
      (empiricalProb (fun ω => e (Z ω)) b'))]
  apply Finset.sum_congr rfl
  intro b _
  have hset : (univ.filter (fun ω => e (Z ω) = e b)) = univ.filter (fun ω => Z ω = b) := by
    apply Finset.filter_congr
    intro ω _
    exact ⟨fun h => e.injective h, fun h => by rw [h]⟩
  simp only [empiricalProb, hset]
  rfl

private lemma shannonEntropy_of_unique {β : Type*} [Fintype β] [DecidableEq β] [Unique β]
    (Z : Ω → β) : shannonEntropy Z = 0 := by
  have hZ : ∀ ω, Z ω = default := fun ω => Subsingleton.elim _ _
  have huniv : (univ : Finset β) = {default} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨mem_univ _, fun x _ => Subsingleton.elim x default⟩
  have hprob : empiricalProb Z default = 1 := by
    unfold empiricalProb
    have hfilt : (univ.filter (fun ω => Z ω = default)) = univ := by
      apply Finset.filter_true_of_mem
      intro ω _; exact hZ ω
    rw [hfilt, Finset.card_univ]
    have : (Fintype.card Ω : ℝ) ≠ 0 := by
      have := Fintype.card_pos (α := Ω); positivity
    field_simp
  unfold shannonEntropy
  rw [huniv, Finset.sum_singleton, hprob]
  simp

end

open Finset in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {n : ℕ} {γ : Type*} [Fintype γ] [DecidableEq γ]
    (Z : Fin n → Ω → γ) :
    shannonEntropy (fun ω i => Z i ω) ≤ ∑ i, shannonEntropy (Z i) := by
  induction n with
  | zero =>
    have : Unique (Fin 0 → γ) := Pi.uniqueOfIsEmpty _
    rw [shannonEntropy_of_unique]
    simp
  | succ n ih =>
    set e : (Fin (n+1) → γ) ≃ γ × (Fin n → γ) :=
      (Equiv.arrowCongr (finSuccEquiv n) (Equiv.refl γ)).trans Equiv.piOptionEquivProd
      with he_def
    have hcomp : (fun ω => e (fun i => Z i ω)) = fun ω => (Z 0 ω, fun i => Z i.succ ω) := by
      funext ω
      simp only [he_def, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.coe_refl,
        Equiv.piOptionEquivProd, Equiv.coe_fn_mk, Function.comp_apply, id_eq]
      refine Prod.ext ?_ ?_
      · simp
      · funext i
        simp
    have hkey := shannonEntropy_comp_equiv e (fun ω i => Z i ω)
    rw [hcomp] at hkey
    rw [← hkey]
    have hstep := shannonEntropy_prod_le (Z 0) (fun (ω : Ω) (i : Fin n) => Z i.succ ω)
    have hind := ih (fun (i : Fin n) => Z i.succ)
    have hsum : ∑ i : Fin (n+1), shannonEntropy (Z i)
        = shannonEntropy (Z 0) + ∑ i : Fin n, shannonEntropy (Z i.succ) := by
      rw [Fin.sum_univ_succ]
    rw [hsum]
    linarith
