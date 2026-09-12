import Mathlib
import Definitions.Def_DiscreteEntropy
import Solutions.Sol_kleitman_diameter

open Finset MeasureTheory ProbabilityTheory

/-! Platform-accepted facts needed for the assembly below, reproduced here
under their proper names. NOTE: `Solutions.Sol_shannonEntropy_pi_le`,
`Solutions.Sol_shannonEntropy_pigeonhole`, `Solutions.Sol_gibbs_inequality`,
`Solutions.Sol_shannonEntropy_prod_le`, and
`Solutions.Sol_choose_sum_le_exp_mul_binEntropy` cannot be imported directly:
each names its main theorem `solution` (a platform grading convention), so
importing more than one at once is a hard name clash, and
`Sol_shannonEntropy_pi_le`/`Sol_shannonEntropy_prod_le` additionally import
the *unsolved* `Theorems.Thm_*` stub of their dependency rather than the
accepted `Solutions.Sol_*` version. The proofs below are copied verbatim
from the accepted Solutions files (only the theorem names and internal
cross-references are fixed up); `Solutions.Sol_kleitman_diameter` is
imported directly above since it is self-contained and already exposes
`kleitman_diameter` under its real name. -/

noncomputable section

variable {γ' : Type*} [Fintype γ']

theorem gibbs_inequality (p q : γ' → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hpq : ∀ x, p x ≠ 0 → q x ≠ 0)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    ∑ x ∈ univ.filter (fun x => p x ≠ 0), p x * Real.log (q x / p x) ≤ 0 := by
  set S := univ.filter (fun x => p x ≠ 0) with hS_def
  have hpsumS : ∑ x ∈ S, p x = 1 := by
    rw [← hpsum, hS_def]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x _ hx
    simp only [Finset.mem_filter, mem_univ, true_and, not_not] at hx
    exact hx
  have hterm : ∀ x ∈ S, p x * Real.log (q x / p x) ≤ q x - p x := by
    intro x hx
    simp only [hS_def, Finset.mem_filter] at hx
    have hpxpos : 0 < p x := lt_of_le_of_ne (hp0 x) (Ne.symm hx.2)
    have hqxpos : 0 < q x := lt_of_le_of_ne (hq0 x) (Ne.symm (hpq x hx.2))
    have hlog : Real.log (q x / p x) ≤ q x / p x - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hqxpos hpxpos)
    calc p x * Real.log (q x / p x) ≤ p x * (q x / p x - 1) :=
          mul_le_mul_of_nonneg_left hlog (hp0 x)
      _ = q x - p x := by field_simp
  have hqsumS : ∑ x ∈ S, q x ≤ ∑ x, q x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro x _ _
    exact hq0 x
  calc ∑ x ∈ S, p x * Real.log (q x / p x)
      ≤ ∑ x ∈ S, (q x - p x) := Finset.sum_le_sum hterm
    _ = (∑ x ∈ S, q x) - ∑ x ∈ S, p x := by rw [Finset.sum_sub_distrib]
    _ ≤ (∑ x, q x) - ∑ x ∈ S, p x := by linarith
    _ = 1 - 1 := by rw [hqsum, hpsumS]
    _ = 0 := by ring

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

theorem shannonEntropy_prod_le {Ω β1 β2 : Type*} [Fintype Ω] [Fintype β1] [Fintype β2]
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

private lemma shannonEntropy_comp_equiv {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {β β' : Type*} [Fintype β] [DecidableEq β]
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

private lemma shannonEntropy_of_unique {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {β : Type*} [Fintype β] [DecidableEq β] [Unique β]
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

theorem shannonEntropy_pi_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
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

private lemma exists_max_empiricalProb {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]
    [Nonempty Ω] (Z : Ω → β) [Nonempty β] :
    ∃ b : β, ∀ b' : β, empiricalProb Z b' ≤ empiricalProb Z b := by
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image (univ : Finset β) (empiricalProb Z) univ_nonempty
  exact ⟨b, fun b' => hb b' (mem_univ b')⟩

private lemma shannonEntropy_ge_neg_logb_max {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]
    [Nonempty Ω] (Z : Ω → β) [Nonempty β] (b : β)
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

theorem shannonEntropy_pigeonhole {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]
    [Nonempty Ω] (Z : Ω → β) [Nonempty β] :
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

theorem choose_sum_le_exp_mul_binEntropy (n k : ℕ) (hn : 0 < n) (hk2 : 2 * k ≤ n) :
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤ Real.exp (n * Real.binEntropy ((k : ℝ) / n)) := by
  set lam : ℝ := (k : ℝ) / n with hlam_def
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlam0 : 0 ≤ lam := by positivity
  have h2k : (2:ℝ) * (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast hk2
  have hnlam0 : (n : ℝ) * lam = k := by rw [hlam_def]; field_simp
  have hlam1 : lam ≤ 1 - lam := by nlinarith [hnlam0, hnR]
  have h1lam_nonneg0 : (0:ℝ) ≤ 1 - lam := by linarith
  have hkey : ∀ j ≤ k, lam ^ k * (1 - lam) ^ (n - k) ≤ lam ^ j * (1 - lam) ^ (n - j) := by
    intro j hjk
    have hnk : n - j = (n - k) + (k - j) := by omega
    rw [hnk, pow_add]
    have hle : lam ^ (k - j) ≤ (1 - lam) ^ (k - j) := pow_le_pow_left₀ hlam0 hlam1 _
    calc lam ^ k * (1 - lam) ^ (n - k)
        = lam ^ j * lam ^ (k - j) * (1 - lam) ^ (n - k) := by
          rw [← pow_add]; congr 2; omega
      _ ≤ lam ^ j * (1 - lam) ^ (k - j) * (1 - lam) ^ (n - k) := by
          have h1lam_nonneg : (0:ℝ) ≤ 1 - lam := by linarith
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = lam ^ j * ((1 - lam) ^ (n - k) * (1 - lam) ^ (k - j)) := by ring
  have hstep : ∀ j ∈ Finset.range (k + 1),
      (n.choose j : ℝ) * (lam ^ k * (1 - lam) ^ (n - k))
        ≤ (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j)) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    exact mul_le_mul_of_nonneg_left (hkey j (by omega)) (by positivity)
  have hsumC : (∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ)) * (lam ^ k * (1 - lam) ^ (n - k))
      ≤ ∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hstep
  have hsum2 : ∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j))
      ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_subset_range.mpr (by omega)
    · intro j _ _
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (pow_nonneg h1lam_nonneg0 _))
  have hbin : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j)) = 1 := by
    have hap := add_pow lam (1 - lam) n
    simp only [add_sub_cancel, one_pow] at hap
    have hreindex : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j))
        = ∑ m ∈ Finset.range (n + 1), lam ^ m * (1 - lam) ^ (n - m) * (n.choose m : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _; ring
    rw [hreindex, ← hap]
  have hfinal : (∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ)) * (lam ^ k * (1 - lam) ^ (n - k)) ≤ 1 := by
    calc (∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ)) * (lam ^ k * (1 - lam) ^ (n - k))
        ≤ ∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j)) := hsumC
      _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j)) := hsum2
      _ = 1 := hbin
  rcases eq_or_lt_of_le hlam0 with hlam0' | hlam0'
  · have hk0 : k = 0 := by
      by_contra hk0'
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0'
      have hlampos : (0:ℝ) < lam := by rw [hlam_def]; positivity
      linarith [hlam0']
    subst hk0
    simp only [hlam_def, Nat.cast_zero, zero_div, Real.binEntropy_zero, mul_zero, Real.exp_zero]
    norm_num
  · have hlam1' : lam < 1 := by linarith
    have hpos : 0 < lam ^ k * (1 - lam) ^ (n - k) := by positivity
    have hdiv : (∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ)) ≤ 1 / (lam ^ k * (1 - lam) ^ (n - k)) := by
      rw [le_div_iff₀ hpos]
      exact hfinal
    refine hdiv.trans (le_of_eq ?_)
    have hkn : k ≤ n := by omega
    have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by push_cast [hkn]; ring
    have hnlam : (n : ℝ) * lam = k := by rw [hlam_def]; field_simp
    have hn1lam : (n : ℝ) * (1 - lam) = (n : ℝ) - k := by
      rw [hlam_def]; field_simp
    have h1lam_pos : (0:ℝ) < 1 - lam := by linarith
    have hRHSpos : (0:ℝ) < lam⁻¹ ^ k * (1 - lam)⁻¹ ^ (n - k) := by positivity
    have hlogRHS : Real.log (lam⁻¹ ^ k * (1 - lam)⁻¹ ^ (n - k))
        = (n : ℝ) * Real.binEntropy lam := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        Real.log_inv, Real.log_inv, hcast, Real.binEntropy, Real.log_inv, Real.log_inv]
      linear_combination (Real.log lam - Real.log (1 - lam)) * hnlam
    rw [← hlogRHS, Real.exp_log hRHSpos, one_div, mul_inv, inv_pow, inv_pow]

/-- Pinsker-type quantitative bound for the binary entropy function (natural-log
based `Real.binEntropy`): the entropy deficit from `log 2` controls how far `p`
is from `1/2`, quadratically. Reused below to get a clean, easy-to-verify bound
on `binEntropy` at a small ratio without computing its value numerically. -/
theorem binEntropy_le_log_two_sub_sq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.binEntropy p ≤ Real.log 2 - 2 * (p - 1/2)^2 := by
  set g : ℝ → ℝ := fun p => Real.binEntropy p + 2 * (p - 1/2)^2 with hg_def
  have hgcont : ContinuousOn g (Set.Icc 0 1) := by
    apply Continuous.continuousOn
    simp only [hg_def]
    fun_prop
  have hgdiff : DifferentiableOn ℝ g (interior (Set.Icc (0:ℝ) 1)) := by
    rw [interior_Icc]
    intro p hp
    rw [Set.mem_Ioo] at hp
    apply DifferentiableAt.differentiableWithinAt
    simp only [hg_def]
    apply DifferentiableAt.add
    · exact Real.differentiableAt_binEntropy hp.1.ne' hp.2.ne
    · fun_prop
  have hderiv_eq : ∀ p ∈ Set.Ioo (0:ℝ) 1, deriv g p = Real.log (1-p) - Real.log p + 4*(p - 1/2) := by
    intro p hp
    rw [Set.mem_Ioo] at hp
    have hbin : HasDerivAt Real.binEntropy (Real.log (1-p) - Real.log p) p :=
      Real.hasDerivAt_binEntropy hp.1.ne' hp.2.ne
    have hquad : HasDerivAt (fun p : ℝ => 2*(p-1/2)^2) (4*(p-1/2)) p := by
      have h1 : HasDerivAt (fun p : ℝ => p - 1/2) 1 p := (hasDerivAt_id p).sub_const _
      have h2 := (h1.fun_pow 2).const_mul (2:ℝ)
      norm_num at h2
      have hval : (4:ℝ) * (p - 1/2) = 2 * (2 * (p - 1/2)) := by ring
      rw [hval]
      exact h2
    have hg' : HasDerivAt g (Real.log (1-p) - Real.log p + 4*(p-1/2)) p := by
      rw [hg_def]; exact hbin.add hquad
    exact hg'.deriv
  have hgdiff' : DifferentiableOn ℝ (deriv g) (interior (Set.Icc (0:ℝ) 1)) := by
    rw [interior_Icc]
    have hmodel : DifferentiableOn ℝ
        (fun p => Real.log (1-p) - Real.log p + 4*(p - 1/2)) (Set.Ioo (0:ℝ) 1) := by
      intro p hp
      rw [Set.mem_Ioo] at hp
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.add
      · apply DifferentiableAt.sub
        · fun_prop (disch := linarith)
        · fun_prop (disch := linarith)
      · fun_prop
    exact hmodel.congr (fun p hp => hderiv_eq p hp)
  have hderiv2_nonpos : ∀ p ∈ interior (Set.Icc (0:ℝ) 1), deriv^[2] g p ≤ 0 := by
    rw [interior_Icc]
    intro p hp
    rw [Set.mem_Ioo] at hp
    have heq2 : deriv^[2] g p = deriv (fun p => Real.log (1-p) - Real.log p + 4*(p - 1/2)) p := by
      rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply]
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [IsOpen.mem_nhds isOpen_Ioo hp] with x hx
      exact hderiv_eq x hx
    rw [heq2]
    have hd1 : HasDerivAt (fun p : ℝ => Real.log (1-p)) (-(1-p)⁻¹) p := by
      have h1 : HasDerivAt (fun p : ℝ => (1:ℝ) - p) (-1) p := by
        simpa using (hasDerivAt_id p).const_sub (1:ℝ)
      have h2 := h1.log (show (1:ℝ) - p ≠ 0 by linarith)
      convert h2 using 1
      field_simp
    have hd2 : HasDerivAt (fun p : ℝ => Real.log p) p⁻¹ p := Real.hasDerivAt_log hp.1.ne'
    have hd3 : HasDerivAt (fun p : ℝ => (4:ℝ)*(p - 1/2)) 4 p := by
      have h1 : HasDerivAt (fun p : ℝ => p - 1/2) 1 p := (hasDerivAt_id p).sub_const _
      simpa using h1.const_mul (4:ℝ)
    have hsum : HasDerivAt (fun p => Real.log (1-p) - Real.log p + 4*(p - 1/2))
        (-(1-p)⁻¹ - p⁻¹ + 4) p := (hd1.sub hd2).add hd3
    rw [hsum.deriv]
    have h14 : p * (1-p) ≤ 1/4 := by nlinarith [sq_nonneg (p - 1/2)]
    have hppos : 0 < p := hp.1
    have h1ppos : 0 < 1 - p := by linarith [hp.2]
    have hinv : 4 ≤ (1-p)⁻¹ + p⁻¹ := by
      rw [inv_add_inv h1ppos.ne' hppos.ne']
      rw [le_div_iff₀ (by positivity)]
      nlinarith [h14]
    linarith [hinv]
  have hconcave : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) g :=
    concaveOn_of_deriv2_nonpos (convex_Icc 0 1) hgcont hgdiff hgdiff' hderiv2_nonpos
  have hsymm : ∀ q ∈ Set.Icc (0:ℝ) 1, g (1 - q) = g q := by
    intro q _
    simp only [hg_def]
    rw [Real.binEntropy_one_sub]
    ring_nf
  have hg_half : g (1/2) = Real.log 2 := by
    simp only [hg_def]
    rw [show (1:ℝ)/2 - 1/2 = 0 by ring]
    simp [Real.binEntropy_two_inv]
  have key : g p ≤ Real.log 2 := by
    rcases lt_trichotomy p (1/2) with hlt | heq | hgt
    · have hx : p ∈ Set.Icc (0:ℝ) 1 := ⟨hp0, hp1⟩
      have hz : (1:ℝ) - p ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith
      have hyz : (1:ℝ)/2 < 1 - p := by linarith
      have hslope := hconcave.slope_anti_adjacent hx hz hlt hyz
      rw [hsymm p ⟨hp0, hp1⟩, show (1:ℝ) - p - 1/2 = 1/2 - p from by ring] at hslope
      have hpos : (0:ℝ) < 1/2 - p := by linarith
      rw [div_le_div_iff_of_pos_right hpos] at hslope
      rw [hg_half] at hslope
      linarith
    · rw [heq, hg_half]
    · have hx : (1:ℝ) - p ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith
      have hz : p ∈ Set.Icc (0:ℝ) 1 := ⟨hp0, hp1⟩
      have hxy : (1:ℝ) - p < 1/2 := by linarith
      have hslope := hconcave.slope_anti_adjacent hx hz hxy hgt
      rw [hsymm p ⟨hp0, hp1⟩, show (1:ℝ)/2 - (1 - p) = p - 1/2 from by ring] at hslope
      have hpos : (0:ℝ) < p - 1/2 := by linarith
      rw [div_le_div_iff_of_pos_right hpos] at hslope
      rw [hg_half] at hslope
      linarith
  simp only [hg_def] at key
  linarith [key]

end

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

-- NOTE: shellIdx (the quantized row-sum) is defined further below, AFTER the
-- Chernoff/measure machinery, using `round` (not `⌊·⌋`) so that there is a
-- single symmetric central bucket rather than two ({-1,0}) -- see
-- scratch/SPENCER_PLAN.md for why the floor convention was abandoned.

/-- The uniform probability measure on `Fin m → Bool`. -/
def uMeasure (m : ℕ) : Measure (Fin m → Bool) :=
  Measure.pi (fun _ : Fin m => (PMF.uniformOfFintype Bool).toMeasure)

instance (m : ℕ) : IsProbabilityMeasure (uMeasure m) := by
  unfold uMeasure; infer_instance

lemma uMeasure_eq_uniform (m : ℕ) :
    uMeasure m = (PMF.uniformOfFintype (Fin m → Bool)).toMeasure := by
  apply Measure.ext_of_singleton
  intro ω
  rw [uMeasure, Measure.pi_singleton]
  have h1 : ∀ i : Fin m, ((PMF.uniformOfFintype Bool).toMeasure) {ω i} = (2 : ENNReal)⁻¹ := by
    intro i
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply]
    norm_num
  simp_rw [h1]
  rw [Finset.prod_const, Finset.card_univ]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply]
  rw [Fintype.card_fun]
  simp only [Fintype.card_bool]
  push_cast
  exact ENNReal.inv_pow.symm

lemma uMeasure_real_coe_finset (m : ℕ) (S : Finset (Fin m → Bool)) :
    (uMeasure m).real (S : Set (Fin m → Bool)) = (S.card : ℝ) / (2 : ℝ) ^ m := by
  rw [Measure.real, uMeasure_eq_uniform, PMF.toMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : Fintype.card (Fin m → Bool) = 2 ^ m := by
    rw [Fintype.card_fun]; simp
  rw [hcard, ENNReal.toReal_mul]
  push_cast
  rw [ENNReal.toReal_inv]
  simp [div_eq_mul_inv]

lemma RSign_indep (m : ℕ) : iIndepFun (fun (j : Fin m) => (fun ω => RSign ω j)) (uMeasure m) := by
  have := iIndepFun_pi (μ := fun _ : Fin m => (PMF.uniformOfFintype Bool).toMeasure)
    (X := fun (_ : Fin m) (b : Bool) => if b then (1:ℝ) else (-1:ℝ))
    (fun _ => by fun_prop)
  exact this

lemma RSign_meas (m : ℕ) (j : Fin m) : AEMeasurable ((fun ω => RSign ω j)) (uMeasure m) := by
  unfold RSign; fun_prop

lemma RSign_mem_Icc (m : ℕ) (j : Fin m) :
    ∀ᵐ ω ∂(uMeasure m), RSign ω j ∈ Set.Icc (-1:ℝ) 1 := by
  filter_upwards with ω
  unfold RSign
  split <;> norm_num

lemma RSign_integral_eq_zero (m : ℕ) (j : Fin m) : (uMeasure m)[(fun ω => RSign ω j)] = 0 := by
  have key := integral_comp_eval (X := fun _ : Fin m => Bool)
    (μ := fun _ : Fin m => (PMF.uniformOfFintype Bool).toMeasure)
    (f := fun b : Bool => if b = true then (1:ℝ) else (-1:ℝ)) (i := j) (by fun_prop)
  show (∫ ω : Fin m → Bool, (fun b : Bool => if b = true then (1:ℝ) else (-1:ℝ)) (ω j)
    ∂(uMeasure m)) = 0
  unfold uMeasure
  rw [key, integral_fintype (by fun_prop)]
  rw [Fintype.sum_bool]
  rw [show ((PMF.uniformOfFintype Bool).toMeasure).real {true} = (2:ℝ)⁻¹ from ?_,
      show ((PMF.uniformOfFintype Bool).toMeasure).real {false} = (2:ℝ)⁻¹ from ?_]
  · norm_num
  · rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (by measurability)]
    rw [PMF.uniformOfFintype_apply]; simp
  · rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (by measurability)]
    rw [PMF.uniformOfFintype_apply]; simp

lemma RSign_subgaussian (m : ℕ) (j : Fin m) :
    HasSubgaussianMGF ((fun ω => RSign ω j)) 1 (uMeasure m) := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := uMeasure m)
    (X := (fun ω => RSign ω j)) (a := -1) (b := 1) (RSign_meas m j) (RSign_mem_Icc m j)
    (RSign_integral_eq_zero m j)
  have heq : (‖(1:ℝ) - (-1)‖₊ / 2) ^ 2 = 1 := by
    have : ‖(1:ℝ) - (-1)‖₊ = 2 := by
      rw [show (1:ℝ) - (-1) = 2 by ring]; ext; simp
    rw [this]; norm_num
  rwa [heq] at h

lemma subgaussian_weaken' {m : ℕ} {X : (Fin m → Bool) → ℝ} {c c' : NNReal}
    (h : HasSubgaussianMGF X c (uMeasure m)) (hc : c ≤ c') :
    HasSubgaussianMGF X c' (uMeasure m) where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := by
    refine (h.mgf_le t).trans (Real.exp_le_exp.mpr ?_)
    have : (c:ℝ) ≤ (c':ℝ) := by exact_mod_cast hc
    nlinarith [sq_nonneg t]

lemma rowSumB_subgaussian (m : ℕ) (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1) :
    HasSubgaussianMGF (rowSumB a) (m : NNReal) (uMeasure m) := by
  have hindep : iIndepFun (fun j : Fin m => fun ω => a j * RSign ω j) (uMeasure m) := by
    have h0 := RSign_indep m
    have h1 := h0.comp (g := fun j : Fin m => fun x : ℝ => a j * x) (fun j => by fun_prop)
    simp only [Function.comp_def] at h1
    exact h1
  have hsub : ∀ j : Fin m, HasSubgaussianMGF (fun ω => a j * RSign ω j)
      (⟨(a j)^2, sq_nonneg _⟩ * 1) (uMeasure m) := by
    intro j
    exact (RSign_subgaussian m j).const_mul (a j)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ) hindep (fun j _ => hsub j)
  have hcard : (∑ j : Fin m, (⟨(a j)^2, sq_nonneg (a j)⟩ * 1 : NNReal)) ≤ (m : NNReal) := by
    rw [show (m : NNReal) = ∑ _j : Fin m, (1:NNReal) by simp]
    apply Finset.sum_le_sum
    intro j _
    show (a j)^2 * 1 ≤ (1:ℝ)
    rcases h01 j with h | h <;> rw [h] <;> norm_num
  have heq : rowSumB a = fun ω => ∑ j : Fin m, a j * RSign ω j := rfl
  rw [heq]
  exact subgaussian_weaken' hsum hcard

lemma rowSumB_tail_bound (m : ℕ) (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (uMeasure m).real {ω | t ≤ |rowSumB a ω|} ≤ 2 * Real.exp (-t^2 / (2 * m)) := by
  have hsub := rowSumB_subgaussian m a h01
  set Y : (Fin m → Bool) → ℝ := rowSumB a with hY
  have hpos : (uMeasure m).real {ω | t ≤ Y ω} ≤ Real.exp (-t^2 / (2 * m)) := by
    have := hsub.measure_ge_le ht
    simpa using this
  have hneg : (uMeasure m).real {ω | t ≤ -Y ω} ≤ Real.exp (-t^2 / (2 * m)) := by
    have hsub' := hsub.neg
    have := hsub'.measure_ge_le ht
    simpa using this
  have hsub_eq : {ω | t ≤ |Y ω|} ⊆ {ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rcases abs_cases (Y ω) with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq] at hω; exact Or.inl hω
    · rw [heq] at hω; exact Or.inr hω
  calc (uMeasure m).real {ω | t ≤ |Y ω|}
      ≤ (uMeasure m).real ({ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω}) := measureReal_mono hsub_eq
    _ ≤ (uMeasure m).real {ω | t ≤ Y ω} + (uMeasure m).real {ω | t ≤ -Y ω} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-t^2 / (2 * m)) + Real.exp (-t^2 / (2 * m)) := add_le_add hpos hneg
    _ = 2 * Real.exp (-t^2 / (2 * m)) := by ring

/-- The quantized (shell-index) row sum: the integer nearest `rowSumB a ω / (2Δ)`.
Using `round` (rather than `⌊·⌋`) gives a single symmetric central bucket
`shellIdx = 0 ↔ |rowSumB| ≤ Δ`, instead of two ({-1,0}) that would each carry
roughly half the probability mass and cost a wasted bit of entropy regardless
of `Δ` -- see scratch/SPENCER_PLAN.md. -/
def shellIdx (a : Fin m → ℝ) (ω : Fin m → Bool) : ℤ := round (rowSumB a ω / (2*Δ))

/-- The defining property of `round`: the quantized value is within `Δ` of the
true row sum. -/
lemma shellIdx_dist (a : Fin m → ℝ) (ω : Fin m → Bool) (hΔpos : 0 < Δ) :
    |rowSumB a ω - 2*Δ*(shellIdx Δ a ω : ℝ)| ≤ Δ := by
  have h := abs_sub_round (rowSumB a ω / (2*Δ))
  unfold shellIdx
  have heq : rowSumB a ω - 2*Δ*(round (rowSumB a ω / (2*Δ)) : ℝ)
      = (2*Δ) * (rowSumB a ω / (2*Δ) - round (rowSumB a ω / (2*Δ))) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Δ)]
  calc 2*Δ * |rowSumB a ω / (2*Δ) - round (rowSumB a ω / (2*Δ))|
      ≤ 2*Δ * (1/2) := by
        apply mul_le_mul_of_nonneg_left h (by positivity)
    _ = Δ := by ring

lemma shellIdx_bound (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1) (hΔ : (1:ℝ)/2 ≤ Δ)
    (ω : Fin m → Bool) :
    (shellIdx Δ a ω : ℝ) ∈ Set.Icc (-((m:ℝ)/(2*Δ) + 1)) ((m:ℝ)/(2*Δ) + 1) := by
  have hΔpos : 0 < Δ := by linarith
  have hb := abs_rowSumB_le a h01 ω
  have hd := shellIdx_dist Δ a ω hΔpos
  rw [abs_le] at hb hd
  have hub : 2*Δ*(shellIdx Δ a ω:ℝ) ≤ (m:ℝ) + 2*Δ := by nlinarith [hb.2, hd.1]
  have hlb : -((m:ℝ) + 2*Δ) ≤ 2*Δ*(shellIdx Δ a ω:ℝ) := by nlinarith [hb.1, hd.2]
  rw [Set.mem_Icc]
  constructor
  · have hstep : (-(shellIdx Δ a ω:ℝ) - 1) * (2*Δ) ≤ (m:ℝ) := by nlinarith [hlb]
    have h2 : -(shellIdx Δ a ω:ℝ) - 1 ≤ (m:ℝ)/(2*Δ) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*Δ)]; exact hstep
    linarith [h2]
  · have hstep : ((shellIdx Δ a ω:ℝ) - 1) * (2*Δ) ≤ (m:ℝ) := by nlinarith [hub]
    have h2 : (shellIdx Δ a ω:ℝ) - 1 ≤ (m:ℝ)/(2*Δ) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*Δ)]; exact hstep
    linarith [h2]

/-- The shell index, packaged into a fixed-size `Fin` type via a shift and a
(never-triggered, for `Δ ≥ 1/2`) safety `%`. -/
def shellFin (Δ : ℝ) (a : Fin m → ℝ) (ω : Fin m → Bool) : Fin (2*m+3) :=
  ⟨(shellIdx Δ a ω + (m+1)).toNat % (2*m+3), Nat.mod_lt _ (by omega)⟩

/-- Shifted `shellIdx` always lands in `[0, 2m+2]` as an integer, for `Δ ≥ 1/2`. -/
lemma shellIdx_shift_range (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1)
    (hΔ : (1:ℝ)/2 ≤ Δ) (ω : Fin m → Bool) :
    0 ≤ shellIdx Δ a ω + (m+1) ∧ (shellIdx Δ a ω + (m+1)).toNat < 2*m+3 := by
  have hb := shellIdx_bound Δ a h01 hΔ ω
  rw [Set.mem_Icc] at hb
  have hle : (m:ℝ)/(2*Δ) ≤ m := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2*Δ)]
    nlinarith [hΔ, (Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hub : (shellIdx Δ a ω : ℝ) ≤ m + 1 := by linarith [hb.2, hle]
  have hlb : -(((m:ℝ)) + 1) ≤ (shellIdx Δ a ω : ℝ) := by linarith [hb.1, hle]
  have hub' : shellIdx Δ a ω ≤ (m:ℤ) + 1 := by exact_mod_cast hub
  have hlb' : -((m:ℤ) + 1) ≤ shellIdx Δ a ω := by exact_mod_cast hlb
  omega

lemma shellFin_eq_toNat (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1)
    (hΔ : (1:ℝ)/2 ≤ Δ) (ω : Fin m → Bool) :
    (shellFin Δ a ω : ℕ) = (shellIdx Δ a ω + (m+1)).toNat := by
  obtain ⟨_, hsmall⟩ := shellIdx_shift_range Δ a h01 hΔ ω
  unfold shellFin
  simp only
  exact Nat.mod_eq_of_lt hsmall

lemma shellFin_eq_iff (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1)
    (hΔ : (1:ℝ)/2 ≤ Δ) (ω : Fin m → Bool) (k : Fin (2*m+3)) :
    shellFin Δ a ω = k ↔ shellIdx Δ a ω = (k : ℤ) - (m+1) := by
  obtain ⟨hnn, _⟩ := shellIdx_shift_range Δ a h01 hΔ ω
  rw [Fin.ext_iff, shellFin_eq_toNat Δ a h01 hΔ ω]
  constructor
  · intro h; omega
  · intro h; omega

/-- The empirical probability of a shell (as a `shellFin` value) equals the
Finset-counting probability of the corresponding `shellIdx` value. -/
lemma empiricalProb_shellFin (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1)
    (hΔ : (1:ℝ)/2 ≤ Δ) (k : Fin (2*m+3)) :
    empiricalProb (shellFin Δ a) k
      = ((univ.filter (fun ω => shellIdx Δ a ω = (k:ℤ) - (m+1))).card : ℝ) / (2:ℝ) ^ m := by
  unfold empiricalProb
  have hcard : Fintype.card (Fin m → Bool) = 2 ^ m := by
    rw [Fintype.card_fun]; simp
  have hfilter : (univ.filter (fun ω => shellFin Δ a ω = k))
      = (univ.filter (fun ω => shellIdx Δ a ω = (k:ℤ) - (m+1))) := by
    apply Finset.filter_congr
    intro ω _
    simp [shellFin_eq_iff Δ a h01 hΔ ω k]
  rw [hfilter, hcard]
  push_cast
  ring

/-- Tail bound for a nonzero shell: `Pr[shellIdx = j] ≤ 2·exp(-λ²(2|j|-1)²/2)`
when `Δ = λ√m` and `j ≠ 0`. -/
lemma shellIdx_prob_le (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1)
    (hΔpos : 0 < Δ) {j : ℤ} (hj : j ≠ 0) :
    ((univ.filter (fun ω => shellIdx Δ a ω = j)).card : ℝ) / (2:ℝ)^m
      ≤ 2 * Real.exp (-(Δ*(2*|(j:ℝ)|-1))^2 / (2*m)) := by
  have hj1 : (1:ℝ) ≤ |(j:ℝ)| := by
    have h1 : (1:ℤ) ≤ |j| := Int.one_le_abs hj
    have h2 : ((|j| : ℤ) : ℝ) = |(j:ℝ)| := by push_cast [Int.cast_abs]; ring
    calc (1:ℝ) = ((1:ℤ):ℝ) := by norm_num
      _ ≤ ((|j| : ℤ) : ℝ) := by exact_mod_cast h1
      _ = |(j:ℝ)| := h2
  rw [← uMeasure_real_coe_finset m (univ.filter (fun ω => shellIdx Δ a ω = j))]
  have hsub : (↑(univ.filter (fun ω => shellIdx Δ a ω = j)) : Set (Fin m → Bool))
      ⊆ {ω | Δ*(2*|(j:ℝ)|-1) ≤ |rowSumB a ω|} := by
    intro ω hω
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
    have hd := shellIdx_dist Δ a ω hΔpos
    rw [hω] at hd
    rw [abs_le] at hd
    rcases abs_cases (j:ℝ) with ⟨hjeq, hjpos⟩ | ⟨hjeq, hjneg⟩
    · rw [hjeq]
      rcases abs_cases (rowSumB a ω) with ⟨hreq, _⟩ | ⟨hreq, hrneg⟩
      · rw [hreq]; nlinarith [hd.1, hd.2]
      · exfalso; nlinarith [hd.1, hd.2, hjpos]
    · rw [hjeq]
      rcases abs_cases (rowSumB a ω) with ⟨hreq, hrpos⟩ | ⟨hreq, _⟩
      · exfalso; nlinarith [hd.1, hd.2, hjneg]
      · rw [hreq]; nlinarith [hd.1, hd.2]
  calc (uMeasure m).real (↑(univ.filter (fun ω => shellIdx Δ a ω = j)) : Set (Fin m → Bool))
      ≤ (uMeasure m).real {ω | Δ*(2*|(j:ℝ)|-1) ≤ |rowSumB a ω|} := measureReal_mono hsub
    _ ≤ 2 * Real.exp (-(Δ*(2*|(j:ℝ)|-1))^2 / (2*m)) :=
        rowSumB_tail_bound m a h01 (Δ*(2*|(j:ℝ)|-1)) (by nlinarith)

/-- Step 5 of the entropy-sum derivation (see scratch/SPENCER_PLAN.md): the
elementary bound `1 + 4Y ≤ 2·exp Y` for `Y ≥ 0`, via a shift of
`Real.add_one_le_exp` by `log 2` together with the numeric fact `log 2 < 3/4`
(`Real.log_two_lt_d9`). -/
lemma key_exp_bound (Y : ℝ) (hY : 0 ≤ Y) : 1 + 4*Y ≤ 2*Real.exp Y := by
  have h1 : 1 + (Y - Real.log 2) ≤ Real.exp (Y - Real.log 2) := by
    linarith [Real.add_one_le_exp (Y - Real.log 2)]
  have h2 : Real.exp (Y - Real.log 2) = Real.exp Y / 2 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  rw [h2] at h1
  have hlog2 : Real.log 2 < 3/4 := by
    have := Real.log_two_lt_d9
    linarith
  linarith [h1, hlog2]

/-- Step 5, in its needed form: `(1+X)·exp(-X/4) ≤ 2` for `X ≥ 0`. -/
lemma one_add_mul_exp_neg_le (X : ℝ) (hX : 0 ≤ X) :
    (1 + X) * Real.exp (-X/4) ≤ 2 := by
  have hY : 0 ≤ X/4 := by linarith
  have hb := key_exp_bound (X/4) hY
  have hexp : Real.exp (X/4) > 0 := Real.exp_pos _
  have h1X : 1 + X ≤ 2 * Real.exp (X/4) := by linarith
  have heq : Real.exp (-X/4) = (Real.exp (X/4))⁻¹ := by
    rw [show -X/4 = -(X/4) by ring, Real.exp_neg]
  rw [heq]
  rw [← div_eq_mul_inv, div_le_iff₀ hexp]
  linarith [h1X]

/-- Step 6a of the entropy-sum derivation: `(2k-1)² ≥ 4k-3` for every real `k`,
with equality at `k=1`. Elementary: `(2k-1)² - (4k-3) = 4(k-1)² ≥ 0`. -/
lemma sq_two_mul_sub_one_ge (k : ℝ) : 4*k - 3 ≤ (2*k-1)^2 := by
  nlinarith [sq_nonneg (k-1)]

/-- The `shannonEntropy` per-outcome term `p ↦ if p = 0 then 0 else p * logb 2 (1/p)`
coincides, for every real `p` (junk values included), with `negMulLog p / log 2`.
This lets us reuse Mathlib's `negMulLog` toolkit (concavity, derivative,
`negMulLog_le_one_sub_self`) directly for entropy terms. -/
lemma entropyTerm_eq_negMulLog_div (p : ℝ) :
    (if p = 0 then (0:ℝ) else p * Real.logb 2 (1 / p)) = Real.negMulLog p / Real.log 2 := by
  by_cases h : p = 0
  · simp [h]
  · rw [if_neg h, ← Real.log_div_log, one_div, Real.log_inv]
    unfold Real.negMulLog
    ring

/-- `negMulLog` is strictly increasing on `[0, 1/e]`, since its derivative
`-log x - 1` is positive exactly when `x < 1/e`. -/
lemma negMulLog_strictMonoOn : StrictMonoOn Real.negMulLog (Set.Icc 0 (Real.exp (-1))) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) Real.continuous_negMulLog.continuousOn
  intro x hx
  rw [interior_Icc, Set.mem_Ioo] at hx
  obtain ⟨hx0, hx1⟩ := hx
  rw [Real.deriv_negMulLog (ne_of_gt hx0)]
  have hlogx : Real.log x < -1 := by
    have := Real.log_lt_log hx0 hx1
    rwa [Real.log_exp] at this
  linarith

/-- Step 2 of the entropy-sum derivation: the entropy-term contribution of a
peripheral (`j ≠ 0`) shell is controlled by `λ²(2|j|-1)²` once `λ ≥ 2`, via
`negMulLog`'s monotonicity on `[0, 1/e]` (the tail bound `q_j` always lands
there for `λ ≥ 2`, `|j| ≥ 1`). -/
lemma peripheral_entropyTerm_le (lam : ℝ) (hlam : 2 ≤ lam) {j : ℤ} (hj : j ≠ 0)
    (p : ℝ) (hp0 : 0 ≤ p)
    (hple : p ≤ 2 * Real.exp (-(lam^2 * (2*|(j:ℝ)|-1)^2 / 2))) :
    (if p = 0 then (0:ℝ) else p * Real.logb 2 (1 / p))
      ≤ (2 * Real.exp (-(lam^2 * (2*|(j:ℝ)|-1)^2 / 2)))
          * (lam^2 * (2*|(j:ℝ)|-1)^2) / (2 * Real.log 2) := by
  have hj1 : (1:ℝ) ≤ |(j:ℝ)| := by
    have h1 : (1:ℤ) ≤ |j| := Int.one_le_abs hj
    calc (1:ℝ) = ((1:ℤ):ℝ) := by norm_num
      _ ≤ ((|j| : ℤ) : ℝ) := by exact_mod_cast h1
      _ = |(j:ℝ)| := by push_cast [Int.cast_abs]; ring
  set X : ℝ := lam^2 * (2*|(j:ℝ)|-1)^2 / 2 with hXdef
  set q : ℝ := 2 * Real.exp (-X) with hqdef
  have hXge : 2 ≤ X := by
    have h1 : (1:ℝ) ≤ 2*|(j:ℝ)|-1 := by linarith
    have h2 : (4:ℝ) ≤ lam^2 := by nlinarith [sq_nonneg (lam - 2)]
    have h3 : (1:ℝ) ≤ (2*|(j:ℝ)|-1)^2 := by nlinarith [sq_nonneg (2*|(j:ℝ)|-1-1)]
    have hprod : (4:ℝ) * 1 ≤ lam^2 * (2*|(j:ℝ)|-1)^2 :=
      mul_le_mul h2 h3 (by norm_num) (by positivity)
    rw [hXdef, le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [hprod]
  have hqpos : 0 < q := by rw [hqdef]; positivity
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hqle : q ≤ Real.exp (-1) := by
    have hexp2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hmono : Real.exp (-X) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
    calc q = 2 * Real.exp (-X) := hqdef
      _ ≤ Real.exp 1 * Real.exp (-2) :=
          mul_le_mul hexp2 hmono (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-1) := by rw [← Real.exp_add]; norm_num
  have hple' : p ≤ q := hple
  have hmem_p : p ∈ Set.Icc (0:ℝ) (Real.exp (-1)) := ⟨hp0, hple'.trans hqle⟩
  have hmem_q : q ∈ Set.Icc (0:ℝ) (Real.exp (-1)) := ⟨hqpos.le, hqle⟩
  have hmono2 : Real.negMulLog p ≤ Real.negMulLog q :=
    negMulLog_strictMonoOn.monotoneOn hmem_p hmem_q hple'
  have hterm_p : (if p = 0 then (0:ℝ) else p * Real.logb 2 (1 / p))
      = Real.negMulLog p / Real.log 2 := entropyTerm_eq_negMulLog_div p
  rw [hterm_p]
  have hlogq : Real.log q = Real.log 2 - X := by
    rw [hqdef, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hstep1 : Real.negMulLog p / Real.log 2 ≤ Real.negMulLog q / Real.log 2 :=
    div_le_div_of_nonneg_right hmono2 hlog2pos.le
  have hstep2 : Real.negMulLog q / Real.log 2 = q * (X - Real.log 2) / Real.log 2 := by
    unfold Real.negMulLog
    rw [hlogq]; ring
  have hlog2ne : Real.log 2 ≠ 0 := hlog2pos.ne'
  have heq2X : q * (2*X) / (2 * Real.log 2) = q * X / Real.log 2 := by
    field_simp
  have hstep3 : q * (X - Real.log 2) / Real.log 2 ≤ q * (2*X) / (2 * Real.log 2) := by
    rw [heq2X]
    have hqle0 : q * (X - Real.log 2) ≤ q * X := by nlinarith [mul_pos hqpos hlog2pos]
    exact div_le_div_of_nonneg_right hqle0 hlog2pos.le
  have hgoaleq : q * (lam^2 * (2*|(j:ℝ)|-1)^2) / (2 * Real.log 2) = q * (2*X) / (2 * Real.log 2) := by
    rw [hXdef]; ring
  rw [hgoaleq]
  calc Real.negMulLog p / Real.log 2 ≤ Real.negMulLog q / Real.log 2 := hstep1
    _ = q * (X - Real.log 2) / Real.log 2 := hstep2
    _ ≤ q * (2*X) / (2 * Real.log 2) := hstep3

/-- Step 1 of the entropy-sum derivation: the central shell's (`j=0`) entropy
term is controlled by its "escaping" mass `1 - p_0`, via the existing Mathlib
bound `Real.negMulLog_le_one_sub_self`. -/
lemma central_entropyTerm_le (p0 : ℝ) (hp0 : 0 ≤ p0) :
    (if p0 = 0 then (0:ℝ) else p0 * Real.logb 2 (1 / p0)) ≤ (1 - p0) / Real.log 2 := by
  rw [entropyTerm_eq_negMulLog_div]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact div_le_div_of_nonneg_right (Real.negMulLog_le_one_sub_self hp0) hlog2pos.le

/-- A finite geometric partial sum, in closed form. -/
lemma geom_partial_sum_eq (r : ℝ) (hr1 : r ≠ 1) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, r ^ k = r * (1 - r ^ N) / (1 - r) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n), ih]
    have h1mr : (1:ℝ) - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
    field_simp
    ring

/-- Step 6b of the entropy-sum derivation: for `0 ≤ r < 1`, a finite geometric
partial sum `Σ_{k=1}^N r^k` is bounded by the full series value `r/(1-r)`. -/
lemma geom_partial_sum_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, r ^ k ≤ r / (1 - r) := by
  rw [geom_partial_sum_eq r (ne_of_lt hr1) N]
  have h1mr : 0 < 1 - r := by linarith
  apply div_le_div_of_nonneg_right _ h1mr.le
  nlinarith [mul_nonneg hr0 (pow_nonneg hr0 N)]

/-- Step 6b, assembled: for `λ ≥ 2`, the finite sum `Σ_{k=1}^N exp(-λ²(2k-1)²/4)`
is bounded by `(16/15)·exp(-λ²/4)`, via step 6a's `(2k-1)² ≥ 4k-3` comparison
to a geometric series with ratio `exp(-λ²) ≤ 1/16`. -/
lemma peripheral_geom_sum_le (lam : ℝ) (hlam : 2 ≤ lam) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, Real.exp (-(lam^2 * (2*(k:ℝ)-1)^2) / 4)
      ≤ (16/15 : ℝ) * Real.exp (-lam^2/4) := by
  set r : ℝ := Real.exp (-(lam^2)) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hrdef]
    calc Real.exp (-(lam^2)) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  have hexp1_ge2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hexp4_eq : Real.exp (4:ℝ) = Real.exp 1 ^ 4 := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have hexp4_ge16 : (16:ℝ) ≤ Real.exp 4 := by
    rw [hexp4_eq]
    calc (16:ℝ) = 2^4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 := by gcongr
  have hexplam2_ge16 : (16:ℝ) ≤ Real.exp (lam^2) := by
    calc (16:ℝ) ≤ Real.exp 4 := hexp4_ge16
      _ ≤ Real.exp (lam^2) := Real.exp_le_exp.mpr (by nlinarith)
  have hr_le : r ≤ 1/16 := by
    rw [hrdef, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hexplam2_ge16
  have hinv_le : (1:ℝ) / (1 - r) ≤ 16/15 := by
    have h1mr : (0:ℝ) < 1 - r := by linarith
    rw [div_le_iff₀ h1mr]
    nlinarith [hr_le]
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      Real.exp (-(lam^2 * (2*(k:ℝ)-1)^2) / 4) ≤ Real.exp (3*lam^2/4) * r^k := by
    intro k _
    rw [hrdef, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h6a := sq_two_mul_sub_one_ge (k:ℝ)
    have hprod : lam^2/4 * (4*(k:ℝ) - 3) ≤ lam^2/4 * (2*(k:ℝ)-1)^2 :=
      mul_le_mul_of_nonneg_left h6a (by positivity)
    nlinarith [hprod]
  calc ∑ k ∈ Finset.Icc 1 N, Real.exp (-(lam^2 * (2*(k:ℝ)-1)^2) / 4)
      ≤ ∑ k ∈ Finset.Icc 1 N, Real.exp (3*lam^2/4) * r^k := Finset.sum_le_sum hterm
    _ = Real.exp (3*lam^2/4) * ∑ k ∈ Finset.Icc 1 N, r^k := by rw [Finset.mul_sum]
    _ ≤ Real.exp (3*lam^2/4) * (r / (1 - r)) := by
        apply mul_le_mul_of_nonneg_left (geom_partial_sum_le r hr0 hr1 N) (Real.exp_pos _).le
    _ = Real.exp (3*lam^2/4) * r * (1/(1-r)) := by ring
    _ ≤ Real.exp (3*lam^2/4) * r * (16/15) := by
        apply mul_le_mul_of_nonneg_left hinv_le
        exact mul_nonneg (Real.exp_pos _).le hr0
    _ = (16/15) * (Real.exp (3*lam^2/4) * r) := by ring
    _ = (16/15) * Real.exp (-lam^2/4) := by
        congr 1
        rw [hrdef, ← Real.exp_add]
        congr 1
        ring

/-- Step 4 of the entropy-sum derivation: reindex the sum over `shellFin`'s
`Fin (2m+3)` codomain to a sum over the integer shell index `j`, ranging over
`Icc (-(m+1)) (m+1)`, via the shift bijection `k ↦ (k:ℤ) - (m+1)`. -/
lemma shellFin_sum_eq_int_sum (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1)
    (hΔ : (1:ℝ)/2 ≤ Δ) (g : ℝ → ℝ) :
    ∑ k : Fin (2*m+3), g (empiricalProb (shellFin Δ a) k)
      = ∑ j ∈ Finset.Icc (-((m:ℤ)+1)) ((m:ℤ)+1),
          g (((univ.filter (fun ω => shellIdx Δ a ω = j)).card : ℝ) / (2:ℝ) ^ m) := by
  apply Finset.sum_nbij' (i := fun k : Fin (2*m+3) => (k:ℤ) - ((m:ℤ)+1))
      (j := fun z : ℤ => (⟨(z + ((m:ℤ)+1)).toNat % (2*m+3), Nat.mod_lt _ (by omega)⟩ : Fin (2*m+3)))
  · intro k _
    have hk : (k:ℕ) < 2*m+3 := k.isLt
    rw [Finset.mem_Icc]
    omega
  · intro z _
    exact Finset.mem_univ _
  · intro k _
    have hk : (k:ℕ) < 2*m+3 := k.isLt
    apply Fin.ext
    dsimp only
    have heq : (k:ℤ) - ((m:ℤ)+1) + ((m:ℤ)+1) = (k:ℤ) := by ring
    rw [heq]
    have hcast : (k:ℤ).toNat = (k:ℕ) := by
      have h0 : (0:ℤ) ≤ (k:ℤ) := Int.natCast_nonneg _
      have h1 := Int.toNat_of_nonneg h0
      exact_mod_cast h1
    rw [hcast]
    exact Nat.mod_eq_of_lt hk
  · intro z hz
    rw [Finset.mem_Icc] at hz
    have hzn : 0 ≤ z + ((m:ℤ)+1) := by omega
    have hzu : (z + ((m:ℤ)+1)).toNat < 2*m+3 := by omega
    have hval : ((⟨(z + ((m:ℤ)+1)).toNat % (2*m+3), Nat.mod_lt _ (by omega)⟩ : Fin (2*m+3)) : ℕ)
        = (z + ((m:ℤ)+1)).toNat := Nat.mod_eq_of_lt hzu
    show (((⟨(z + ((m:ℤ)+1)).toNat % (2*m+3), Nat.mod_lt _ (by omega)⟩ : Fin (2*m+3)) : ℕ) : ℤ)
        - ((m:ℤ)+1) = z
    rw [hval]
    omega
  · intro k _
    rw [empiricalProb_shellFin Δ a h01 hΔ k]

/-- The remaining half of step 4: pair up `j` and `-j` in a sum over
`Icc (-N) N` with `0` removed, folding it into a sum over `Icc 1 N`. Pure
integer combinatorics, no probability content. -/
lemma sum_erase_zero_Icc_eq (N : ℕ) (h : ℤ → ℝ) :
    ∑ j ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0, h j
      = ∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ), (h k + h (-k)) := by
  have hsplit : (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0
      = Finset.Icc (-(N:ℤ)) (-1) ∪ Finset.Icc (1:ℤ) (N:ℤ) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc (-(N:ℤ)) (-1)) (Finset.Icc (1:ℤ) (N:ℤ)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_Icc] at hx1 hx2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hneg : ∑ x ∈ Finset.Icc (-(N:ℤ)) (-1), h x = ∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ), h (-k) := by
    apply Finset.sum_nbij' (i := fun x : ℤ => -x) (j := fun x : ℤ => -x)
    · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
    · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
    · intro x _; ring
    · intro x _; ring
    · intro x _; rw [neg_neg]
  rw [hneg, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Bridge lemma: a sum over `Finset.Icc (1:ℤ) N` equals the corresponding
sum over `Finset.Icc (1:ℕ) N`, via the obvious `ℕ ↔ ℤ` bijection on that
range. Pure integer/natural combinatorics, needed to connect
`sum_erase_zero_Icc_eq` (stated over `ℤ`) with `peripheral_geom_sum_le`
(stated over `ℕ`). -/
lemma sum_Icc_int_nat_eq (N : ℕ) (h : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ), h k = ∑ k ∈ Finset.Icc 1 N, h (k:ℤ) := by
  apply Finset.sum_nbij' (i := fun k : ℤ => k.toNat) (j := fun k : ℕ => (k:ℤ))
  · intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    omega
  · intro k _
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    congr 1
    omega

/-- **Lemma 9** (final assembly): for `Δ = λ√m` with `λ ≥ 2`, `m ≥ 1`, the
Shannon entropy of the quantized row-sum is bounded by `(12/log 2)·e^{-λ²/4}`.
Assembles all seven steps of the hand-derived proof in `SPENCER_PLAN.md`. -/
theorem shannonEntropy_shellFin_le (hm : 1 ≤ m) (a : Fin m → ℝ)
    (h01 : ∀ j, a j = 0 ∨ a j = 1) (lam : ℝ) (hlam : 2 ≤ lam) :
    shannonEntropy (shellFin (lam * Real.sqrt (m:ℝ)) a)
      ≤ (12 / Real.log 2) * Real.exp (-lam^2/4) := by
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  have hsqrtm1 : (1:ℝ) ≤ Real.sqrt (m:ℝ) := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hmR
  set Δ : ℝ := lam * Real.sqrt (m:ℝ) with hΔdef
  have hΔge : lam ≤ Δ := by rw [hΔdef]; nlinarith [hsqrtm1]
  have hΔ : (1:ℝ)/2 ≤ Δ := by linarith
  have hΔpos : 0 < Δ := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hΔsq : Δ^2 = lam^2 * (m:ℝ) := by
    rw [hΔdef, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  have key_identity : ∀ (y:ℝ), (Δ*y)^2/(2*(m:ℝ)) = lam^2*y^2/2 := by
    intro y
    rw [mul_pow, hΔsq]
    field_simp
  have hexp_eq : ∀ (j:ℤ),
      (-(Δ*(2*|(j:ℝ)|-1))^2/(2*(m:ℝ))) = (-(lam^2*(2*|(j:ℝ)|-1)^2/2)) := by
    intro j
    rw [neg_div, key_identity (2*|(j:ℝ)|-1)]
  have hqbound : ∀ (j:ℤ), j ≠ 0 →
      ((univ.filter (fun ω => shellIdx Δ a ω = j)).card : ℝ) / (2:ℝ)^m
        ≤ 2 * Real.exp (-(lam^2*(2*|(j:ℝ)|-1)^2/2)) := by
    intro j hj
    rw [← hexp_eq j]
    exact shellIdx_prob_le Δ a h01 hΔpos hj
  unfold shannonEntropy
  set f : ℝ → ℝ := fun p => if p = 0 then (0:ℝ) else p * Real.logb 2 (1 / p) with hfdef
  rw [shellFin_sum_eq_int_sum Δ a h01 hΔ f]
  set P : ℤ → ℝ := fun j => ((univ.filter (fun ω => shellIdx Δ a ω = j)).card : ℝ) / (2:ℝ)^m
    with hPdef
  set N : ℕ := m + 1 with hNdef
  have hIccEq : Finset.Icc (-((m:ℤ)+1)) ((m:ℤ)+1) = Finset.Icc (-(N:ℤ)) (N:ℤ) := by
    have h1 : (-((m:ℤ)+1)) = (-(N:ℤ)) := by rw [hNdef]; push_cast; ring
    have h2 : ((m:ℤ)+1) = (N:ℤ) := by rw [hNdef]; push_cast; ring
    rw [h1, h2]
  rw [hIccEq]
  have h0mem : (0:ℤ) ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) := by
    rw [Finset.mem_Icc]
    have : (0:ℤ) ≤ (N:ℤ) := Int.natCast_nonneg N
    omega
  have hins : Finset.Icc (-(N:ℤ)) (N:ℤ)
      = insert (0:ℤ) ((Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0) := (Finset.insert_erase h0mem).symm
  have hsum_one : ∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), P j = 1 := by
    have hid := shellFin_sum_eq_int_sum Δ a h01 hΔ id
    simp only [id_eq] at hid
    rw [hIccEq] at hid
    rw [← hid]
    exact sum_empiricalProb (shellFin Δ a)
  have hnotmem : (0:ℤ) ∉ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0 := by simp
  rw [hins, Finset.sum_insert hnotmem] at hsum_one ⊢
  have hP0_eq : 1 - P 0 = ∑ j ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0, P j := by
    linarith [hsum_one]
  have hPnonneg : ∀ j : ℤ, 0 ≤ P j := by
    intro j
    rw [hPdef]
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) m)
  -- Reusable bound on Σ_{erase 0} q_j (q_j := 2·exp(-λ²(2|j|-1)²/2))
  have hq_erase_le : ∑ j ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0,
      2*Real.exp (-(lam^2*(2*|(j:ℝ)|-1)^2/2)) ≤ (64/15) * Real.exp (-lam^2/4) := by
    rw [sum_erase_zero_Icc_eq N (fun j => 2*Real.exp (-(lam^2*(2*|(j:ℝ)|-1)^2/2)))]
    have hterm : ∀ k ∈ Finset.Icc (1:ℤ) (N:ℤ),
        (2*Real.exp (-(lam^2*(2*|(k:ℝ)|-1)^2/2))
          + 2*Real.exp (-(lam^2*(2*|((-k:ℤ):ℝ)|-1)^2/2)))
        ≤ 4*Real.exp (-(lam^2*(2*(k:ℝ)-1)^2)/4) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hkpos : (0:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by linarith : (0:ℤ) ≤ k)
      have hkabs : |(k:ℝ)| = (k:ℝ) := abs_of_nonneg hkpos
      have hnegk : ((-k:ℤ):ℝ) = -(k:ℝ) := by push_cast; ring
      have hnegkabs : |((-k:ℤ):ℝ)| = (k:ℝ) := by rw [hnegk, abs_neg, hkabs]
      rw [hkabs, hnegkabs]
      have h6a := sq_two_mul_sub_one_ge (k:ℝ)
      have hprod : lam^2/4 * (4*(k:ℝ) - 3) ≤ lam^2/4 * (2*(k:ℝ)-1)^2 :=
        mul_le_mul_of_nonneg_left h6a (by positivity)
      have hhalf : -(lam^2*(2*(k:ℝ)-1)^2/2) ≤ -(lam^2*(2*(k:ℝ)-1)^2)/4 := by nlinarith
      have hexple : Real.exp (-(lam^2*(2*(k:ℝ)-1)^2/2)) ≤ Real.exp (-(lam^2*(2*(k:ℝ)-1)^2)/4) :=
        Real.exp_le_exp.mpr hhalf
      linarith [hexple]
    calc ∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ),
          (2*Real.exp (-(lam^2*(2*|(k:ℝ)|-1)^2/2)) + 2*Real.exp (-(lam^2*(2*|((-k:ℤ):ℝ)|-1)^2/2)))
        ≤ ∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ), 4*Real.exp (-(lam^2*(2*(k:ℝ)-1)^2)/4) := Finset.sum_le_sum hterm
      _ = 4 * ∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ), Real.exp (-(lam^2*(2*(k:ℝ)-1)^2)/4) := by
          rw [Finset.mul_sum]
      _ = 4 * ∑ k ∈ Finset.Icc 1 N, Real.exp (-(lam^2*(2*(k:ℝ)-1)^2)/4) := by
          congr 1
          rw [sum_Icc_int_nat_eq N (fun k => Real.exp (-(lam^2*(2*(k:ℝ)-1)^2)/4))]
          apply Finset.sum_congr rfl
          intro k _
          congr 1
      _ ≤ 4 * ((16/15) * Real.exp (-lam^2/4)) :=
          mul_le_mul_of_nonneg_left (peripheral_geom_sum_le lam hlam N) (by norm_num)
      _ = (64/15) * Real.exp (-lam^2/4) := by ring
  have hperiph_prob_le : ∑ j ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0, P j
      ≤ (64/15) * Real.exp (-lam^2/4) := by
    calc ∑ j ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0, P j
        ≤ ∑ j ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0,
            2*Real.exp (-(lam^2*(2*|(j:ℝ)|-1)^2/2)) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_erase] at hj
          exact hqbound j hj.1
      _ ≤ (64/15) * Real.exp (-lam^2/4) := hq_erase_le
  have hcentral : f (P 0) ≤ (64/15)/Real.log 2 * Real.exp (-lam^2/4) := by
    calc f (P 0) ≤ (1 - P 0)/Real.log 2 :=
          central_entropyTerm_le (P 0) (hPnonneg 0)
      _ = (∑ j ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0, P j)/Real.log 2 := by rw [hP0_eq]
      _ ≤ ((64/15) * Real.exp (-lam^2/4))/Real.log 2 :=
          div_le_div_of_nonneg_right hperiph_prob_le hlog2pos.le
      _ = (64/15)/Real.log 2 * Real.exp (-lam^2/4) := by ring
  have hperiph : ∑ j ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0, f (P j)
      ≤ (64/15)/Real.log 2 * Real.exp (-lam^2/4) := by
    calc ∑ j ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0, f (P j)
        ≤ ∑ j ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0,
            (2*Real.exp (-(lam^2*(2*|(j:ℝ)|-1)^2/2))) * (lam^2*(2*|(j:ℝ)|-1)^2) / (2*Real.log 2) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_erase] at hj
          exact peripheral_entropyTerm_le lam hlam hj.1 (P j) (hPnonneg j)
            (hqbound j hj.1)
      _ ≤ (64/15)/Real.log 2 * Real.exp (-lam^2/4) := by
          rw [sum_erase_zero_Icc_eq N (fun j =>
            (2*Real.exp (-(lam^2*(2*|(j:ℝ)|-1)^2/2))) * (lam^2*(2*|(j:ℝ)|-1)^2) / (2*Real.log 2))]
          have hterm : ∀ k ∈ Finset.Icc (1:ℤ) (N:ℤ),
              ((2*Real.exp (-(lam^2*(2*|(k:ℝ)|-1)^2/2))) * (lam^2*(2*|(k:ℝ)|-1)^2) / (2*Real.log 2)
                + (2*Real.exp (-(lam^2*(2*|((-k:ℤ):ℝ)|-1)^2/2)))
                    * (lam^2*(2*|((-k:ℤ):ℝ)|-1)^2) / (2*Real.log 2))
              ≤ 4*Real.exp (-(lam^2*(2*(k:ℝ)-1)^2)/4) / Real.log 2 := by
            intro k hk
            rw [Finset.mem_Icc] at hk
            have hkpos : (0:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by linarith : (0:ℤ) ≤ k)
            have hkabs : |(k:ℝ)| = (k:ℝ) := abs_of_nonneg hkpos
            have hnegk : ((-k:ℤ):ℝ) = -(k:ℝ) := by push_cast; ring
            have hnegkabs : |((-k:ℤ):ℝ)| = (k:ℝ) := by rw [hnegk, abs_neg, hkabs]
            rw [hkabs, hnegkabs]
            set X : ℝ := lam^2*(2*(k:ℝ)-1)^2 with hXdef
            have hXnn : 0 ≤ X := by rw [hXdef]; positivity
            have hXexp4 : X * Real.exp (-X/4) ≤ 2 := by
              have hkey := one_add_mul_exp_neg_le X hXnn
              nlinarith [hkey, Real.exp_pos (-X/4)]
            have hexp_split : Real.exp (-(X/2)) = Real.exp (-X/4) * Real.exp (-X/4) := by
              rw [← Real.exp_add]; congr 1; ring
            have hXX : X * Real.exp (-(X/2)) ≤ 2 * Real.exp (-X/4) := by
              rw [hexp_split, ← mul_assoc]
              exact mul_le_mul_of_nonneg_right hXexp4 (Real.exp_pos _).le
            have heq : (2*Real.exp (-(X/2))) * X / (2*Real.log 2)
                = (X * Real.exp (-(X/2))) / Real.log 2 := by field_simp
            have hbound1 : (2*Real.exp (-(X/2))) * X / (2*Real.log 2)
                ≤ 2*Real.exp (-X/4) / Real.log 2 := by
              rw [heq]
              exact div_le_div_of_nonneg_right hXX hlog2pos.le
            have hdouble2 : (X * Real.exp (-(X/2)))/Real.log 2 + (X * Real.exp (-(X/2)))/Real.log 2
                = 2*(X*Real.exp (-(X/2)))/Real.log 2 := by ring
            have : 2*(X*Real.exp (-(X/2)))/Real.log 2 ≤ 4*Real.exp (-X/4) / Real.log 2 := by
              rw [div_le_div_iff₀ hlog2pos hlog2pos]
              nlinarith [hXX, hlog2pos]
            linarith [heq, hdouble2, this]
          calc ∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ),
                ((2*Real.exp (-(lam^2*(2*|(k:ℝ)|-1)^2/2))) * (lam^2*(2*|(k:ℝ)|-1)^2) / (2*Real.log 2)
                  + (2*Real.exp (-(lam^2*(2*|((-k:ℤ):ℝ)|-1)^2/2)))
                      * (lam^2*(2*|((-k:ℤ):ℝ)|-1)^2) / (2*Real.log 2))
              ≤ ∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ), 4*Real.exp (-(lam^2*(2*(k:ℝ)-1)^2)/4) / Real.log 2 :=
                Finset.sum_le_sum hterm
            _ = (4/Real.log 2) * ∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ),
                  Real.exp (-(lam^2*(2*(k:ℝ)-1)^2)/4) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _
                ring
            _ = (4/Real.log 2) * ∑ k ∈ Finset.Icc 1 N, Real.exp (-(lam^2*(2*(k:ℝ)-1)^2)/4) := by
                congr 1
                rw [sum_Icc_int_nat_eq N (fun k => Real.exp (-(lam^2*(2*(k:ℝ)-1)^2)/4))]
                apply Finset.sum_congr rfl
                intro k _
                congr 1
            _ ≤ (4/Real.log 2) * ((16/15) * Real.exp (-lam^2/4)) :=
                mul_le_mul_of_nonneg_left (peripheral_geom_sum_le lam hlam N) (by positivity)
            _ = (64/15)/Real.log 2 * Real.exp (-lam^2/4) := by ring
  have hgoal12 : (64/15)/Real.log 2 * Real.exp (-lam^2/4) + (64/15)/Real.log 2 * Real.exp (-lam^2/4)
      ≤ (12/Real.log 2) * Real.exp (-lam^2/4) := by
    have hexppos : 0 < Real.exp (-lam^2/4) := Real.exp_pos _
    have heq1 : (64/15)/Real.log 2 * Real.exp (-lam^2/4) + (64/15)/Real.log 2 * Real.exp (-lam^2/4)
        = (128/15) * (Real.exp (-lam^2/4) / Real.log 2) := by ring
    have heq2 : (12/Real.log 2) * Real.exp (-lam^2/4) = 12 * (Real.exp (-lam^2/4) / Real.log 2) := by
      ring
    rw [heq1, heq2]
    exact mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg hexppos.le hlog2pos.le)
  linarith [hcentral, hperiph, hgoal12]

/-- **Lemma 8** (Rothvoss/Spencer, one round of the partial-coloring
schedule): given `n` rows on an `m`-element active set (0/1 coefficients),
and `λ ≥ 2` satisfying the entropy budget `n·(12/log 2)·e^{-λ²/4} ≤ m/10`,
there exist two colorings `x y : Fin m → Bool` at Hamming distance
`> 2·(m/10)` (nat division) such that, writing `χ j := (RSign x j - RSign
y j)/2` for the signed half-difference, every row `i` has
`|Σ_j a i j · χ j| ≤ λ√m`. This is the joint-entropy analogue of
Rothvoss's Lemma 8: instead of a per-row union bound, it bounds all `n`
row failures jointly via the entropy bound `shannonEntropy_shellFin_le`
(Lemma 9) combined across rows by `shannonEntropy_pi_le`. -/
theorem lemma8_partial_coloring_round (n : ℕ) (a : Fin n → Fin m → ℝ)
    (h01 : ∀ i j, a i j = 0 ∨ a i j = 1) (hm : 1 ≤ m) (lam : ℝ) (hlam : 2 ≤ lam)
    (hbudget : (n:ℝ) * ((12 / Real.log 2) * Real.exp (-lam^2/4)) ≤ (m:ℝ)/10) :
    ∃ x y : Fin m → Bool,
      2 * (m/10) < (univ.filter (fun j => x j ≠ y j)).card ∧
      ∀ i : Fin n, |∑ j, a i j * ((RSign x j - RSign y j)/2)| ≤ lam * Real.sqrt (m:ℝ) := by
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Δ : ℝ := lam * Real.sqrt (m:ℝ) with hΔdef
  have hsqrtm1 : (1:ℝ) ≤ Real.sqrt (m:ℝ) := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hmR
  have hΔge : lam ≤ Δ := by rw [hΔdef]; nlinarith [hsqrtm1]
  have hΔ : (1:ℝ)/2 ≤ Δ := by linarith
  have hΔpos : 0 < Δ := by linarith
  -- The joint (all-n-rows) quantized shell-vector and its entropy bound.
  set Z : Fin n → (Fin m → Bool) → Fin (2*m+3) := fun i χ => shellFin Δ (a i) χ with hZdef
  set Z' : (Fin m → Bool) → (Fin n → Fin (2*m+3)) := fun χ i => Z i χ with hZ'def
  have hH : shannonEntropy Z' ≤ (m:ℝ)/10 := by
    have hjoint : shannonEntropy Z' ≤ ∑ i, shannonEntropy (Z i) := shannonEntropy_pi_le Z
    have hrow : ∀ i : Fin n, shannonEntropy (Z i) ≤ (12/Real.log 2) * Real.exp (-lam^2/4) :=
      fun i => shannonEntropy_shellFin_le hm (a i) (h01 i) lam hlam
    have hsum_le : ∑ i : Fin n, shannonEntropy (Z i)
        ≤ (n:ℝ) * ((12/Real.log 2) * Real.exp (-lam^2/4)) := by
      calc ∑ i : Fin n, shannonEntropy (Z i)
          ≤ ∑ _i : Fin n, (12/Real.log 2) * Real.exp (-lam^2/4) :=
            Finset.sum_le_sum (fun i _ => hrow i)
        _ = (n:ℝ) * ((12/Real.log 2) * Real.exp (-lam^2/4)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    linarith [hjoint, hsum_le, hbudget]
  -- Pigeonhole: some bucket `b` has an exponentially large fiber `A`.
  have : Nonempty (Fin n → Fin (2*m+3)) := ⟨fun _ => ⟨0, by omega⟩⟩
  obtain ⟨b, hb⟩ := shannonEntropy_pigeonhole Z'
  set A : Finset (Fin m → Bool) := univ.filter (fun χ => Z' χ = b) with hAdef
  have hcardΩ : (Fintype.card (Fin m → Bool) : ℝ) = Real.exp ((m:ℝ) * Real.log 2) := by
    have h1 : Fintype.card (Fin m → Bool) = 2^m := by rw [Fintype.card_fun]; simp
    have h2 : Real.exp ((m:ℝ) * Real.log 2) = (2:ℝ)^m := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    rw [h1, h2]
    push_cast
    ring
  have hrpow : (2:ℝ)^(-shannonEntropy Z') = Real.exp (-shannonEntropy Z' * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), mul_comm]
  have hAcard_ge : Real.exp (((m:ℝ) - shannonEntropy Z') * Real.log 2) ≤ (A.card : ℝ) := by
    have hb' := hb
    rw [hcardΩ, hrpow, ← Real.exp_add] at hb'
    rwa [show (m:ℝ) * Real.log 2 + -shannonEntropy Z' * Real.log 2
        = ((m:ℝ) - shannonEntropy Z') * Real.log 2 by ring] at hb'
  have hAcard_ge2 : Real.exp ((9*(m:ℝ)/10) * Real.log 2) ≤ (A.card : ℝ) := by
    calc Real.exp ((9*(m:ℝ)/10) * Real.log 2)
        ≤ Real.exp (((m:ℝ) - shannonEntropy Z') * Real.log 2) := by
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_right _ hlog2pos.le
          linarith [hH]
      _ ≤ (A.card : ℝ) := hAcard_ge
  -- Kleitman's diameter theorem, via a binEntropy bound on the choose-sum.
  set s : ℕ := m / 10 with hsdef
  have hsm : (10:ℕ) * s ≤ m := by rw [hsdef, mul_comm]; exact Nat.div_mul_le_self m 10
  have h2sm : 2 * s < m := by omega
  have hchooseR : (∑ i ∈ Finset.range (s + 1), (m.choose i : ℝ))
      ≤ Real.exp ((m:ℝ) * Real.binEntropy ((s:ℝ)/m)) :=
    choose_sum_le_exp_mul_binEntropy m s hm (by omega)
  have hsm_ratio : (s:ℝ)/(m:ℝ) ≤ 1/10 := by
    rw [div_le_div_iff₀ hmpos (by norm_num : (0:ℝ) < 10)]
    have h10s : ((10*s : ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast hsm
    push_cast at h10s
    linarith [h10s]
  have hsm_nonneg : (0:ℝ) ≤ (s:ℝ)/(m:ℝ) := by positivity
  have hsm_le1 : (s:ℝ)/(m:ℝ) ≤ 1 := by linarith [hsm_ratio]
  have hbin_le : Real.binEntropy ((s:ℝ)/m) ≤ Real.log 2 - 2*((s:ℝ)/m - 1/2)^2 :=
    binEntropy_le_log_two_sub_sq ((s:ℝ)/m) hsm_nonneg hsm_le1
  have hsq_ge : (0.4:ℝ)^2 ≤ ((s:ℝ)/m - 1/2)^2 := by nlinarith [hsm_ratio]
  have hbin_lt : Real.binEntropy ((s:ℝ)/m) < (9/10) * Real.log 2 := by
    have hlog2_bd : Real.log 2 < 3.2 := by linarith [Real.log_two_lt_d9]
    nlinarith [hbin_le, hsq_ge, hlog2_bd]
  have hexp_lt : Real.exp ((m:ℝ) * Real.binEntropy ((s:ℝ)/m))
      < Real.exp ((9*(m:ℝ)/10) * Real.log 2) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_lt_mul_of_pos_left hbin_lt hmpos]
  have hchoose_lt : (∑ i ∈ Finset.range (s + 1), (m.choose i : ℝ)) < (A.card : ℝ) :=
    lt_of_le_of_lt hchooseR hexp_lt |>.trans_le hAcard_ge2
  have hchoose_lt_nat : (∑ i ∈ Finset.range (s + 1), m.choose i) < A.card := by
    exact_mod_cast hchoose_lt
  have hcardι : Fintype.card (Fin m) = m := Fintype.card_fin m
  have hAhyp : (∑ i ∈ Finset.range (s + 1), (Fintype.card (Fin m)).choose i) < A.card := by
    rwa [hcardι]
  have hsι : 2 * s < Fintype.card (Fin m) := by rwa [hcardι]
  obtain ⟨x, hxA, y, hyA, hdist⟩ := kleitman_diameter s hsι A hAhyp
  refine ⟨x, y, hdist, ?_⟩
  have hxmem : ∀ i, shellFin Δ (a i) x = b i := by
    intro i
    have hx := hxA
    rw [hAdef, Finset.mem_filter] at hx
    exact congrFun hx.2 i
  have hymem : ∀ i, shellFin Δ (a i) y = b i := by
    intro i
    have hy := hyA
    rw [hAdef, Finset.mem_filter] at hy
    exact congrFun hy.2 i
  intro i
  have heqshell : shellFin Δ (a i) x = shellFin Δ (a i) y := by rw [hxmem i, hymem i]
  have heqidx : shellIdx Δ (a i) x = shellIdx Δ (a i) y := by
    have h1 : shellIdx Δ (a i) x = (shellFin Δ (a i) x : ℤ) - (m+1) :=
      (shellFin_eq_iff Δ (a i) (h01 i) hΔ x (shellFin Δ (a i) x)).mp rfl
    have h2 : shellIdx Δ (a i) y = (shellFin Δ (a i) y : ℤ) - (m+1) :=
      (shellFin_eq_iff Δ (a i) (h01 i) hΔ y (shellFin Δ (a i) y)).mp rfl
    rw [h1, h2, heqshell]
  have hdx := shellIdx_dist Δ (a i) x hΔpos
  have hdy := shellIdx_dist Δ (a i) y hΔpos
  rw [heqidx] at hdx
  have hdiff : |rowSumB (a i) x - rowSumB (a i) y| ≤ 2*Δ := by
    have htri := abs_sub_le (rowSumB (a i) x) (2*Δ*(shellIdx Δ (a i) y:ℝ)) (rowSumB (a i) y)
    have hcomm : |2*Δ*(shellIdx Δ (a i) y:ℝ) - rowSumB (a i) y|
        = |rowSumB (a i) y - 2*Δ*(shellIdx Δ (a i) y:ℝ)| := abs_sub_comm _ _
    rw [hcomm] at htri
    calc |rowSumB (a i) x - rowSumB (a i) y|
        ≤ |rowSumB (a i) x - 2*Δ*(shellIdx Δ (a i) y:ℝ)|
          + |rowSumB (a i) y - 2*Δ*(shellIdx Δ (a i) y:ℝ)| := htri
      _ ≤ Δ + Δ := add_le_add hdx hdy
      _ = 2*Δ := by ring
  have hrel : rowSumB (a i) x - rowSumB (a i) y
      = 2 * ∑ j, a i j * ((RSign x j - RSign y j)/2) := by
    unfold rowSumB
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hrel, abs_mul, show |(2:ℝ)| = 2 from by norm_num] at hdiff
  linarith [hdiff]

end

/-! ## The outer geometric iteration: telescoping-sum bound

`lemma8_partial_coloring_round` gives ONE round's contribution
`λ(m)·√m` where `λ(m)` is chosen fresh from whatever the ACTUAL active
size `m` happens to be at that round (never from a pre-committed
round-index guess — the active size can shrink faster than the
guaranteed 10% per round, and a λ sized for an over-estimate of `m`
would be too small for the real, smaller `m`). Iterating from `m₀ = n`
down through active sizes `m₀ ≥ m₁ ≥ m₂ ≥ …`, each satisfying
`m_{k+1} ≤ 0.9·m_k` (guaranteed by Lemma 8, regardless of how much
extra got colored), the total row bound is `Σ_k λ(m_k)·√(m_k)`.

Since `λ(m)·√m` is monotone increasing in `m` (checked: for `m ≤ n`,
`m·ln(C/m)` is increasing whenever `m < C/e`, which holds throughout
since `C := 120n/log2 ≈ 173n ≫ n·e`), and `m_k ≤ n·0.9^k` (a genuine
upper bound, provable by a simple induction, unaffected by rounds
over-performing), we get `λ(m_k)·√(m_k) ≤ λ(n·0.9^k)·√(n·0.9^k)`
termwise — so the (variable-length, run-dependent) actual sum is
bounded by the sum of this explicit, IDEALIZED round-indexed sequence,
for ANY number of terms. That idealized sum is what's bounded below:
it decays geometrically (`0.9^{k/2}`) despite `λ` growing like
`√(log(1/0.9^k))` — a genuinely converging series, bounded here via
comparison to a arithmetic-geometric series `Σ(k+1)r^k`, which has a
clean closed form. -/

noncomputable section

/-- The λ that makes `lemma8_partial_coloring_round`'s entropy budget
`n·(12/log2)·exp(-λ²/4) ≤ m/10` hold with EQUALITY at active size `m`
(for fixed total row count `n`). -/
def iterLam (n m : ℝ) : ℝ := 2 * Real.sqrt (Real.log (120*n/(m*Real.log 2)))

/-- The per-round row-bound contribution `λ(m)·√m`. -/
def iterX (n m : ℝ) : ℝ := iterLam n m * Real.sqrt m

/-- `iterLam` exactly saturates the entropy budget: plugging it into
`lemma8_partial_coloring_round`'s hypothesis gives equality, hence `≤`. -/
lemma iterLam_budget_eq (n m : ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) :
    n * ((12/Real.log 2) * Real.exp (-(iterLam n m)^2/4)) = m/10 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hCpos : 0 < 120*n/(m*Real.log 2) := by positivity
  unfold iterLam
  rw [show (2 * Real.sqrt (Real.log (120*n/(m*Real.log 2))))^2
      = 4 * Real.log (120*n/(m*Real.log 2)) by
        rw [mul_pow, Real.sq_sqrt (Real.log_nonneg ?_)]
        · ring
        · rw [le_div_iff₀ (by positivity : (0:ℝ) < m*Real.log 2)]
          nlinarith [hn, hm, hmn, hlog2pos, hlog2lt1,
            mul_le_mul_of_nonneg_left hlog2lt1.le hm.le]]
  rw [show -(4 * Real.log (120*n/(m*Real.log 2)))/4 = -Real.log (120*n/(m*Real.log 2)) by ring,
    Real.exp_neg, Real.exp_log hCpos]
  field_simp
  ring

/-- `Real.sqrt` commutes with natural powers, for a nonneg base. -/
lemma real_sqrt_pow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : Real.sqrt (x^k) = (Real.sqrt x)^k := by
  induction k with
  | zero => simp
  | succ j ih => rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hx j), ih]

/-- Closed form for `Σ_{k=0}^{N-1} (k+1)·r^k`, needed to bound the
polynomial-times-geometric series arising from `λ`'s slow logarithmic
growth against the geometric shrinkage of the active set. -/
lemma arith_geom_partial_sum_eq (r : ℝ) (hr1 : r ≠ 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k:ℝ)+1) * r^k
      = (1 - r^N)/(1-r)^2 - (N:ℝ)*r^N/(1-r) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1mr : (1:ℝ) - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
    push_cast
    field_simp
    ring

lemma arith_geom_partial_sum_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k:ℝ)+1) * r^k ≤ 1/(1-r)^2 := by
  rw [arith_geom_partial_sum_eq r (ne_of_lt hr1) N]
  have h1mr : 0 < 1 - r := by linarith
  have h1 : (1-r^N)/(1-r)^2 ≤ 1/(1-r)^2 :=
    div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 N]) (by positivity)
  have h2 : 0 ≤ (N:ℝ)*r^N/(1-r) := by positivity
  linarith [h1, h2]

/-- The idealized (round-indexed) telescoping-sum bound: no matter how
many rounds `N` are used, `Σ_{k<N} iterX n (n·(9/10)^k) ≤ [explicit
constant]·√n`. The geometric decay `(√(9/10))^k` beats the logarithmic
growth of `iterLam`, so the series converges to an absolute
(n-independent) multiple of `√n`. -/
lemma iterX_sum_le (n : ℝ) (hn : 0 < n) (N : ℕ) :
    ∑ k ∈ Finset.range N, iterX n (n * (9/10)^k)
      ≤ 2 * Real.sqrt (Real.log (120/Real.log 2) + Real.log (10/9))
          * (1 / (1 - Real.sqrt (9/10)))^2 * Real.sqrt n := by
  set A : ℝ := Real.log (120/Real.log 2) with hAdef
  set B : ℝ := Real.log (10/9) with hBdef
  set ρ : ℝ := Real.sqrt (9/10) with hρdef
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hne_log2 : Real.log 2 ≠ 0 := hlog2pos.ne'
  have hne_n : (n:ℝ) ≠ 0 := ne_of_gt hn
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ < 1 := by
    rw [hρdef, show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hApos : 0 < A := by
    rw [hAdef]; apply Real.log_pos; rw [lt_div_iff₀ hlog2pos]; nlinarith [Real.log_two_lt_d9]
  have hBpos : 0 < B := Real.log_pos (by norm_num)
  have hterm : ∀ k ∈ Finset.range N,
      iterX n (n * (9/10)^k) ≤ 2*Real.sqrt (A+B) * ((k:ℝ)+1) * ρ^k * Real.sqrt n := by
    intro k _
    have hne_p : ((9:ℝ)/10)^k ≠ 0 := by positivity
    have heq1 : iterLam n (n * (9/10)^k) = 2 * Real.sqrt (A + (k:ℝ)*B) := by
      unfold iterLam
      congr 2
      have hkey : (120:ℝ)*n/(n*(9/10)^k*Real.log 2) = (120/Real.log 2) * (10/9)^k := by
        rw [show (10:ℝ)/9 = ((9:ℝ)/10)⁻¹ by norm_num, inv_pow]
        field_simp
      rw [hkey, Real.log_mul (by positivity) (by positivity), Real.log_pow, hAdef, hBdef]
    have heq2 : Real.sqrt (n * (9/10)^k) = Real.sqrt n * ρ^k := by
      rw [Real.sqrt_mul hn.le, hρdef, real_sqrt_pow (9/10) (by norm_num) k]
    have hle : Real.sqrt (A + (k:ℝ)*B) ≤ Real.sqrt (A+B) * ((k:ℝ)+1) := by
      have hsq : (A + (k:ℝ)*B) ≤ (A+B)*((k:ℝ)+1)^2 := by
        nlinarith [sq_nonneg ((k:ℝ)), hApos.le, hBpos.le, (Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ))]
      calc Real.sqrt (A + (k:ℝ)*B) ≤ Real.sqrt ((A+B)*((k:ℝ)+1)^2) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (A+B) * ((k:ℝ)+1) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    unfold iterX
    rw [heq1, heq2]
    calc 2 * Real.sqrt (A + (k:ℝ)*B) * (Real.sqrt n * ρ^k)
        ≤ 2 * (Real.sqrt (A+B) * ((k:ℝ)+1)) * (Real.sqrt n * ρ^k) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left hle (by norm_num)
      _ = 2*Real.sqrt (A+B) * ((k:ℝ)+1) * ρ^k * Real.sqrt n := by ring
  calc ∑ k ∈ Finset.range N, iterX n (n * (9/10)^k)
      ≤ ∑ k ∈ Finset.range N, 2*Real.sqrt (A+B) * ((k:ℝ)+1) * ρ^k * Real.sqrt n :=
        Finset.sum_le_sum hterm
    _ = 2*Real.sqrt (A+B) * Real.sqrt n * ∑ k ∈ Finset.range N, ((k:ℝ)+1)*ρ^k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ ≤ 2*Real.sqrt (A+B) * Real.sqrt n * (1/(1-ρ)^2) := by
        apply mul_le_mul_of_nonneg_left (arith_geom_partial_sum_le ρ hρ0 hρ1 N)
        positivity
    _ = 2*Real.sqrt (A+B) * (1/(1-ρ))^2 * Real.sqrt n := by
        rw [div_pow, one_pow]; ring

end

/-! ## The Finset-indexed wrapper: avoiding cross-round `Fin` merging

The inductive construction below needs to apply
`lemma8_partial_coloring_round` to a SHRINKING SUBSET of a FIXED index
type `Fin n` (never to a genuinely different `Fin m` at each level), so
that combining one round's result with the recursive call's result never
requires relating two unrelated `Fin` types — both live in `Fin n → ℝ`/
`Fin n → Bool` throughout, and the "active set" is tracked as a
`Finset (Fin n)` that only shrinks. This wrapper performs the (single,
local) `Finset ≃ Fin card` conversion needed to invoke Lemma 8, then
transports the result straight back to `Fin n`-indexed data. -/

noncomputable section

theorem lemma8_finset_round (n : ℕ) (S : Finset (Fin n)) (a : Fin n → Fin n → ℝ)
    (h01 : ∀ i j, a i j = 0 ∨ a i j = 1) (hS : 1 ≤ S.card) (lam : ℝ) (hlam : 2 ≤ lam)
    (hbudget : (n:ℝ) * ((12/Real.log 2) * Real.exp (-lam^2/4)) ≤ (S.card:ℝ)/10) :
    ∃ χ : Fin n → ℝ, (∀ j, χ j = 0 ∨ χ j = 1 ∨ χ j = -1) ∧ (∀ j, j ∉ S → χ j = 0) ∧
      2*(S.card/10) < (S.filter (fun j => χ j ≠ 0)).card ∧
      ∀ i : Fin n, |∑ j ∈ S, a i j * χ j| ≤ lam * Real.sqrt (S.card:ℝ) := by
  set e := S.equivFin with hedef
  set a' : Fin n → Fin S.card → ℝ := fun i k => a i ((e.symm k : ↥S) : Fin n) with ha'def
  have h01' : ∀ i (k : Fin S.card), a' i k = 0 ∨ a' i k = 1 := fun i k => h01 i _
  obtain ⟨x, y, hdist, hbound⟩ := lemma8_partial_coloring_round n a' h01' hS lam hlam hbudget
  set χ : Fin n → ℝ := fun j =>
    if hj : j ∈ S then (RSign x (e ⟨j, hj⟩) - RSign y (e ⟨j, hj⟩))/2 else 0 with hχdef
  have hinv1 : ∀ (j : Fin n) (hj : j ∈ S), ((e.symm (e ⟨j, hj⟩) : ↥S) : Fin n) = j :=
    fun j hj => congrArg Subtype.val (e.symm_apply_apply ⟨j, hj⟩)
  have hinv2 : ∀ (k : Fin S.card), e ⟨((e.symm k : ↥S) : Fin n), (e.symm k).2⟩ = k := by
    intro k
    have hcast : (⟨((e.symm k : ↥S) : Fin n), (e.symm k).2⟩ : ↥S) = e.symm k := Subtype.ext rfl
    rw [hcast]
    exact e.apply_symm_apply k
  refine ⟨χ, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ S
    · rw [hχdef]
      simp only [dif_pos hj]
      unfold RSign
      rcases x (e ⟨j, hj⟩) <;> rcases y (e ⟨j, hj⟩) <;> norm_num
    · rw [hχdef]; simp [dif_neg hj]
  · intro j hj
    rw [hχdef]; simp [dif_neg hj]
  · have hcard : (S.filter (fun j => χ j ≠ 0)).card
        = (univ.filter (fun k : Fin S.card => x k ≠ y k)).card := by
      apply Finset.card_bij' (i := fun j hj => e ⟨j, (Finset.mem_filter.mp hj).1⟩)
        (j := fun k _ => ((e.symm k : ↥S) : Fin n))
      case hi =>
        intro j hj
        have hjS : j ∈ S := (Finset.mem_filter.mp hj).1
        have hne : χ j ≠ 0 := (Finset.mem_filter.mp hj).2
        rw [hχdef] at hne
        simp only [dif_pos hjS] at hne
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        show x (e ⟨j, hjS⟩) ≠ y (e ⟨j, hjS⟩)
        intro heq
        apply hne
        unfold RSign
        rw [heq]
        ring
      case hj =>
        intro k hk
        have hxy : x k ≠ y k := (Finset.mem_filter.mp hk).2
        rw [Finset.mem_filter]
        refine ⟨(e.symm k).2, ?_⟩
        show χ ((e.symm k : ↥S) : Fin n) ≠ 0
        rw [hχdef]
        simp only [dif_pos (e.symm k).2]
        rw [hinv2]
        intro heq
        apply hxy
        rcases hxv : x k <;> rcases hyv : y k <;> simp_all [RSign] <;> norm_num at heq
      case left_inv =>
        intro j hj
        exact hinv1 j (Finset.mem_filter.mp hj).1
      case right_inv =>
        intro k _
        exact hinv2 k
    rw [hcard]
    exact hdist
  · intro i
    have heq : ∑ j ∈ S, a i j * χ j = ∑ k : Fin S.card, a' i k * ((RSign x k - RSign y k)/2) := by
      apply Finset.sum_bij' (i := fun j hj => e ⟨j, hj⟩) (j := fun k _ => ((e.symm k : ↥S) : Fin n))
      case hi => intro j _; exact Finset.mem_univ _
      case hj => intro k _; exact (e.symm k).2
      case left_neg => intro j hj; exact hinv1 j hj
      case right_neg => intro k _; exact hinv2 k
      case h =>
        intro j hj
        rw [ha'def, hχdef]
        simp only [dif_pos hj]
        rw [hinv1 j hj]
    rw [heq]
    exact hbound i

end

/-! ## The strong-induction construction

Repeatedly apply `lemma8_finset_round` on a shrinking `Finset (Fin n)`,
tracking the round index `k` against the idealized schedule `n·(9/10)^k`
so that `iterX_sum_le` bounds the total accumulated row-discrepancy by an
absolute (run-length-independent) multiple of `√n`. -/

noncomputable section

/-- `iterX n ·` is monotone increasing on `(0, n]`: writing
`C := 120n/log2`, `iterX n m = 2√(C · negMulLog(m/C))`, and since
`m/C ≤ n/C ≪ 1/e` throughout, this reduces to `negMulLog`'s known
monotonicity on `[0, 1/e]`. -/
lemma iterX_mono (n : ℝ) (hn : 0 < n) {m1 m2 : ℝ} (hm1 : 0 < m1) (hm12 : m1 ≤ m2)
    (hm2n : m2 ≤ n) : iterX n m1 ≤ iterX n m2 := by
  set C : ℝ := 120*n/Real.log 2 with hCdef
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hkey : ∀ m : ℝ, 0 < m → m ≤ n →
      iterX n m = 2 * Real.sqrt (C * Real.negMulLog (m / C)) := by
    intro m hm hmn
    have hCn : n ≤ C := by
      rw [hCdef, le_div_iff₀ hlog2pos]
      nlinarith [Real.log_two_lt_d9]
    have hmC : m ≤ C := hmn.trans hCn
    have hCm_ge1 : (1:ℝ) ≤ C/m := (one_le_div hm).mpr hmC
    have hlogCm_nonneg : 0 ≤ Real.log (C/m) := Real.log_nonneg hCm_ge1
    have hlogmC : Real.log (m/C) = - Real.log (C/m) := by
      rw [Real.log_div hm.ne' hCpos.ne', Real.log_div hCpos.ne' hm.ne']; ring
    have hCmC : C * Real.negMulLog (m / C) = m * Real.log (C / m) := by
      unfold Real.negMulLog
      rw [hlogmC]
      field_simp
    have heqarg : (120*n/(m*Real.log 2)) = C/m := by rw [hCdef]; ring
    unfold iterX iterLam
    rw [heqarg, mul_assoc, ← Real.sqrt_mul hlogCm_nonneg, mul_comm (Real.log (C/m)) m, ← hCmC]
  rw [hkey m1 hm1 (hm12.trans hm2n), hkey m2 (hm1.trans_le hm12) hm2n]
  have hlog2lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hexp1lt : Real.exp 1 < 120 := by linarith [Real.exp_one_lt_d9]
  have hnC_le : n / C ≤ Real.exp (-1) := by
    have hnC_eq : n / C = Real.log 2 / 120 := by rw [hCdef]; field_simp
    rw [hnC_eq, Real.exp_neg, inv_eq_one_div]
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 120) (Real.exp_pos 1)]
    nlinarith [mul_lt_mul_of_pos_right hlog2lt1 (Real.exp_pos 1), hexp1lt]
  have hm1_mem : m1/C ∈ Set.Icc (0:ℝ) (Real.exp (-1)) :=
    ⟨div_nonneg hm1.le hCpos.le, by
      have := div_le_div_of_nonneg_right (hm12.trans hm2n) hCpos.le
      linarith [this, hnC_le]⟩
  have hm2_mem : m2/C ∈ Set.Icc (0:ℝ) (Real.exp (-1)) :=
    ⟨div_nonneg (hm1.trans_le hm12).le hCpos.le, by
      have := div_le_div_of_nonneg_right hm2n hCpos.le
      linarith [this, hnC_le]⟩
  have hle : m1/C ≤ m2/C := by
    apply div_le_div_of_nonneg_right hm12 hCpos.le
  have hmono := negMulLog_strictMonoOn.monotoneOn hm1_mem hm2_mem hle
  have hmul : C * Real.negMulLog (m1/C) ≤ C * Real.negMulLog (m2/C) :=
    mul_le_mul_of_nonneg_left hmono hCpos.le
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmul) (by norm_num)

/-- Peel off rounds of `lemma8_finset_round` from a shrinking active
`Finset (Fin n)`, choosing `λ` FRESH from the actual current active size
each round (never from a pre-committed schedule), and tracking the round
index `k` against the idealized upper bound `n·(9/10)^k` on the actual
active size purely as a bookkeeping device for the final total. -/
theorem spencer_partial_coloring (n : ℕ) (hn : 0 < n) (a : Fin n → Fin n → ℝ)
    (h01 : ∀ i j, a i j = 0 ∨ a i j = 1) :
    ∀ m : ℕ, ∀ S : Finset (Fin n), S.card = m → ∀ k : ℕ,
      (m:ℝ) ≤ (n:ℝ) * (9/10)^k →
      ∃ (ε : Fin n → Bool) (K : ℕ),
        ∀ i, |∑ j ∈ S, a i j * RSign ε j|
          ≤ ∑ k' ∈ Finset.range K, iterX (n:ℝ) ((n:ℝ) * (9/10)^(k+k')) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro S hScard k hk
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · refine ⟨fun _ => true, 0, ?_⟩
      have hSempty : S = ∅ := Finset.card_eq_zero.mp (by rw [hScard]; exact hm0)
      intro i
      simp [hSempty]
    · have hmn : m ≤ n := by
        have h1 : S.card ≤ n := by
          have h2 := Finset.card_le_univ S
          rwa [Fintype.card_fin] at h2
        rw [hScard] at h1; exact h1
      have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hmpos
      have hmnR : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      set lam : ℝ := iterLam (n:ℝ) (m:ℝ) with hlamdef
      have hlam2 : 2 ≤ lam := by
        have hstep : (120:ℝ)/Real.log 2 ≤ 120*(n:ℝ)/((m:ℝ)*Real.log 2) := by
          rw [div_le_div_iff₀ hlog2pos (mul_pos hmR hlog2pos)]
          nlinarith [mul_le_mul_of_nonneg_right hmnR hlog2pos.le]
        have h120 : Real.exp 1 ≤ (120:ℝ)/Real.log 2 := by
          rw [le_div_iff₀ hlog2pos]
          have hp : Real.exp 1 * Real.log 2 < 2.7182818286 * 0.6931471808 :=
            mul_lt_mul'' Real.exp_one_lt_d9 Real.log_two_lt_d9 (Real.exp_pos 1).le hlog2pos.le
          nlinarith [hp]
        have harg : Real.exp 1 ≤ 120*(n:ℝ)/((m:ℝ)*Real.log 2) := h120.trans hstep
        have hlog_ge1 : (1:ℝ) ≤ Real.log (120*(n:ℝ)/((m:ℝ)*Real.log 2)) := by
          have := Real.log_le_log (Real.exp_pos 1) harg
          rwa [Real.log_exp] at this
        have hsqrt_ge1 : (1:ℝ) ≤ Real.sqrt (Real.log (120*(n:ℝ)/((m:ℝ)*Real.log 2))) := by
          rw [show (1:ℝ) = Real.sqrt 1 by simp]
          exact Real.sqrt_le_sqrt hlog_ge1
        rw [hlamdef]; unfold iterLam; linarith [hsqrt_ge1]
      have hbudgetS : (n:ℝ) * ((12/Real.log 2) * Real.exp (-lam^2/4)) ≤ (S.card:ℝ)/10 := by
        rw [hScard, hlamdef]
        exact le_of_eq (iterLam_budget_eq (n:ℝ) (m:ℝ) hnR hmR hmnR)
      have hScard1 : 1 ≤ S.card := by rw [hScard]; exact hmpos
      obtain ⟨χ, hχ013, hχsupp, hdist, hbound⟩ :=
        lemma8_finset_round n S a h01 hScard1 lam hlam2 hbudgetS
      classical
      set S' : Finset (Fin n) := S.filter (fun j => χ j = 0) with hS'def
      have hpart_card : S'.card + (S.filter (fun j => ¬ (χ j = 0))).card = S.card :=
        Finset.card_filter_add_card_filter_not (s := S) (fun j => χ j = 0)
      have hdist' : 2*(S.card/10) < (S.filter (fun j => ¬ (χ j = 0))).card := hdist
      have hS'card_lt' : S'.card < S.card := by omega
      have hshrink : 10 * S'.card ≤ 9 * S.card := by omega
      have hS'card_lt : S'.card < m := by rw [← hScard]; exact hS'card_lt'
      have hshrinkR : (S'.card:ℝ) ≤ (9/10) * (S.card:ℝ) := by
        have h10 : (10:ℝ) * (S'.card:ℝ) ≤ 9 * (S.card:ℝ) := by exact_mod_cast hshrink
        linarith
      have hS'k1 : (S'.card:ℝ) ≤ (n:ℝ) * (9/10)^(k+1) := by
        calc (S'.card:ℝ) ≤ (9/10) * (S.card:ℝ) := hshrinkR
          _ = (9/10) * (m:ℝ) := by rw [hScard]
          _ ≤ (9/10) * ((n:ℝ)*(9/10)^k) := by nlinarith [hk]
          _ = (n:ℝ) * (9/10)^(k+1) := by ring
      obtain ⟨ε', K', hbound'⟩ := IH S'.card hS'card_lt S' rfl (k+1) hS'k1
      set ε : Fin n → Bool := fun j => if χ j = 0 then ε' j else decide (χ j = 1) with hεdef
      refine ⟨ε, K'+1, ?_⟩
      intro i
      have hcolored_eq : ∀ j ∈ S.filter (fun j => ¬ (χ j = 0)), RSign ε j = χ j := by
        intro j hj
        have hjne : ¬ (χ j = 0) := (Finset.mem_filter.mp hj).2
        have hεj : ε j = decide (χ j = 1) := by rw [hεdef]; simp [hjne]
        unfold RSign
        rw [hεj]
        rcases hχ013 j with h1 | h1 | h1
        · exact absurd h1 hjne
        · norm_num [h1]
        · norm_num [h1]
      have hS'_eq : ∀ j ∈ S', RSign ε j = RSign ε' j := by
        intro j hj
        have hjeq0 : χ j = 0 := (Finset.mem_filter.mp hj).2
        have hεj : ε j = ε' j := by rw [hεdef]; simp [hjeq0]
        unfold RSign
        rw [hεj]
      have hsum_colored_eq : ∑ j ∈ S.filter (fun j => ¬ (χ j = 0)), a i j * RSign ε j
          = ∑ j ∈ S.filter (fun j => ¬ (χ j = 0)), a i j * χ j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcolored_eq j hj]
      have hsum_S'_eq : ∑ j ∈ S', a i j * RSign ε j = ∑ j ∈ S', a i j * RSign ε' j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hS'_eq j hj]
      have hsplit : ∑ j ∈ S', a i j * RSign ε j
            + ∑ j ∈ S.filter (fun j => ¬ (χ j = 0)), a i j * RSign ε j
          = ∑ j ∈ S, a i j * RSign ε j :=
        Finset.sum_filter_add_sum_filter_not S (fun j => χ j = 0) (fun j => a i j * RSign ε j)
      have hzero_on_S' : ∀ j ∈ S', a i j * χ j = 0 := by
        intro j hj
        have hjeq0 : χ j = 0 := (Finset.mem_filter.mp hj).2
        rw [hjeq0, mul_zero]
      have hsum_split_χ : ∑ j ∈ S.filter (fun j => ¬ (χ j = 0)), a i j * χ j
          = ∑ j ∈ S, a i j * χ j := by
        have hh := Finset.sum_filter_add_sum_filter_not S (fun j => χ j = 0) (fun j => a i j * χ j)
        rw [Finset.sum_eq_zero hzero_on_S'] at hh
        linarith [hh]
      have hkey_eq : ∑ j ∈ S, a i j * RSign ε j
          = ∑ j ∈ S, a i j * χ j + ∑ j ∈ S', a i j * RSign ε' j := by
        rw [← hsplit, hsum_S'_eq, hsum_colored_eq, hsum_split_χ]
        ring
      rw [hkey_eq]
      have habs : |∑ j ∈ S, a i j * χ j + ∑ j ∈ S', a i j * RSign ε' j|
          ≤ |∑ j ∈ S, a i j * χ j| + |∑ j ∈ S', a i j * RSign ε' j| := abs_add_le _ _
      refine habs.trans ?_
      have h1 : |∑ j ∈ S, a i j * χ j| ≤ lam * Real.sqrt (S.card:ℝ) := hbound i
      have h2 : |∑ j ∈ S', a i j * RSign ε' j|
          ≤ ∑ k'' ∈ Finset.range K', iterX (n:ℝ) ((n:ℝ) * (9/10)^(k+1+k'')) := hbound' i
      have h3 : lam * Real.sqrt (S.card:ℝ) = iterX (n:ℝ) (m:ℝ) := by
        rw [hlamdef]; unfold iterX; rw [hScard]
      have hpow_le1 : ((9:ℝ)/10)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hm2n : (n:ℝ)*(9/10)^k ≤ (n:ℝ) := by nlinarith [hpow_le1, hnR]
      have h4 : iterX (n:ℝ) (m:ℝ) ≤ iterX (n:ℝ) ((n:ℝ)*(9/10)^k) :=
        iterX_mono (n:ℝ) hnR hmR hk hm2n
      have heqsum : ∑ k'' ∈ Finset.range K', iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+1+k''))
          = ∑ k' ∈ Finset.range K', iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+(k'+1))) := by
        apply Finset.sum_congr rfl
        intro k' _
        have heq : k+1+k' = k+(k'+1) := by ring
        rw [heq]
      have h5 : iterX (n:ℝ) ((n:ℝ)*(9/10)^k)
            + ∑ k'' ∈ Finset.range K', iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+1+k''))
          = ∑ k' ∈ Finset.range (K'+1), iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+k')) := by
        rw [Finset.sum_range_succ', heqsum]
        have heq0 : k+0 = k := by ring
        rw [heq0]
        ring
      calc |∑ j ∈ S, a i j * χ j| + |∑ j ∈ S', a i j * RSign ε' j|
          ≤ lam * Real.sqrt (S.card:ℝ)
              + ∑ k'' ∈ Finset.range K', iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+1+k'')) :=
            add_le_add h1 h2
        _ = iterX (n:ℝ) (m:ℝ)
              + ∑ k'' ∈ Finset.range K', iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+1+k'')) := by rw [h3]
        _ ≤ iterX (n:ℝ) ((n:ℝ)*(9/10)^k)
              + ∑ k'' ∈ Finset.range K', iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+1+k'')) := by
            linarith [h4]
        _ = ∑ k' ∈ Finset.range (K'+1), iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+k')) := h5

/-- Final assembly: for an `n×n` `{0,1}`-matrix, there is a `±1` coloring
whose signed row sums are all bounded by an explicit, `n`-independent
multiple of `√n`. -/
theorem spencer_sqrt_n_coloring (n : ℕ) (hn : 0 < n) (a : Fin n → Fin n → ℝ)
    (h01 : ∀ i j, a i j = 0 ∨ a i j = 1) :
    ∃ ε : Fin n → Bool, ∀ i, |∑ j, a i j * RSign ε j|
      ≤ 2 * Real.sqrt (Real.log (120/Real.log 2) + Real.log (10/9))
          * (1 / (1 - Real.sqrt (9/10)))^2 * Real.sqrt (n:ℝ) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hk0 : (n:ℝ) ≤ (n:ℝ) * (9/10)^(0:ℕ) := by norm_num
  obtain ⟨ε, K, hK⟩ := spencer_partial_coloring n hn a h01 n Finset.univ (by simp) 0 hk0
  refine ⟨ε, ?_⟩
  intro i
  have h1 : |∑ j ∈ (Finset.univ : Finset (Fin n)), a i j * RSign ε j|
      ≤ ∑ k' ∈ Finset.range K, iterX (n:ℝ) ((n:ℝ)*(9/10)^(0+k')) := hK i
  have h2 : ∑ k' ∈ Finset.range K, iterX (n:ℝ) ((n:ℝ)*(9/10)^(0+k'))
      = ∑ k' ∈ Finset.range K, iterX (n:ℝ) ((n:ℝ)*(9/10)^k') := by
    apply Finset.sum_congr rfl; intro k' _; norm_num
  rw [h2] at h1
  exact h1.trans (iterX_sum_le (n:ℝ) hn0 K)

end
