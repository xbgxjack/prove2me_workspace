import Theorems.Thm_kleitman_diameter
import Theorems.Thm_choose_sum_le_exp_mul_binEntropy
import Mathlib

open Finset MeasureTheory ProbabilityTheory Real
open scoped Classical

namespace Komlos

noncomputable section

variable {n : ℕ} (A : Fin n → Fin n → ℝ) (T : Finset (Fin n))

/-- The finite sample space of `|T|` independent fair coin flips, one per column in `T`. -/
abbrev TOmega (T : Finset (Fin n)) := (↥T → Bool)

/-- The uniform (i.i.d. fair-coin) probability measure on `TOmega T`. -/
def TMeasure (T : Finset (Fin n)) : Measure (TOmega T) :=
  Measure.pi (fun _ : ↥T => (PMF.uniformOfFintype Bool).toMeasure)

instance : IsProbabilityMeasure (TMeasure T) := by
  unfold TMeasure; infer_instance

lemma TMeasure_eq_uniform : TMeasure T = (PMF.uniformOfFintype (TOmega T)).toMeasure := by
  apply MeasureTheory.Measure.ext_of_singleton
  intro ω
  rw [TMeasure, Measure.pi_singleton]
  have h1 : ∀ i : ↥T, (PMF.uniformOfFintype Bool).toMeasure {ω i} = (2 : ENNReal)⁻¹ := by
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

lemma TMeasure_real_coe_finset (S : Finset (TOmega T)) :
    (TMeasure T).real (S : Set (TOmega T)) = (S.card : ℝ) / (2 : ℝ) ^ T.card := by
  rw [Measure.real, TMeasure_eq_uniform, PMF.toMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : Fintype.card (TOmega T) = 2 ^ T.card := by
    rw [Fintype.card_fun]; simp [Fintype.card_coe]
  rw [hcard, ENNReal.toReal_mul]
  push_cast
  rw [ENNReal.toReal_inv]
  simp [div_eq_mul_inv]

/-- `j`-th coordinate's Rademacher (±1) random variable, for `j` a column in `T`. -/
def tF (j : ↥T) (ω : TOmega T) : ℝ := if ω j then (1 : ℝ) else (-1 : ℝ)

lemma tF_indep : iIndepFun (fun (j : ↥T) => tF T j) (TMeasure T) := by
  have := iIndepFun_pi (μ := fun _ : ↥T => (PMF.uniformOfFintype Bool).toMeasure)
    (X := fun (_ : ↥T) (b : Bool) => if b then (1:ℝ) else (-1:ℝ))
    (fun _ => by fun_prop)
  exact this

lemma tF_meas (j : ↥T) : AEMeasurable (tF T j) (TMeasure T) := by
  unfold tF; fun_prop

lemma tF_mem_Icc (j : ↥T) : ∀ᵐ ω ∂(TMeasure T), tF T j ω ∈ Set.Icc (-1:ℝ) 1 := by
  filter_upwards with ω
  unfold tF
  split <;> norm_num

lemma tF_integral_eq_zero (j : ↥T) : (TMeasure T)[tF T j] = 0 := by
  have key := integral_comp_eval (X := fun _ : ↥T => Bool)
    (μ := fun _ : ↥T => (PMF.uniformOfFintype Bool).toMeasure)
    (f := fun b : Bool => if b = true then (1:ℝ) else (-1:ℝ)) (i := j) (by fun_prop)
  show (∫ ω : TOmega T, (fun b : Bool => if b = true then (1:ℝ) else (-1:ℝ)) (ω j)
    ∂(TMeasure T)) = 0
  unfold TMeasure
  rw [key, integral_fintype (by fun_prop)]
  rw [Fintype.sum_bool]
  rw [show ((PMF.uniformOfFintype Bool).toMeasure).real {true} = (2:ℝ)⁻¹ from ?_,
      show ((PMF.uniformOfFintype Bool).toMeasure).real {false} = (2:ℝ)⁻¹ from ?_]
  · norm_num
  · rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (by measurability)]
    rw [PMF.uniformOfFintype_apply]
    simp
  · rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (by measurability)]
    rw [PMF.uniformOfFintype_apply]
    simp

lemma tF_subgaussian (j : ↥T) :
    HasSubgaussianMGF (tF T j) 1 (TMeasure T) := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := TMeasure T)
    (X := tF T j) (a := -1) (b := 1) (tF_meas T j) (tF_mem_Icc T j) (tF_integral_eq_zero T j)
  have heq : (‖(1:ℝ) - (-1)‖₊ / 2) ^ 2 = 1 := by
    have : ‖(1:ℝ) - (-1)‖₊ = 2 := by
      rw [show (1:ℝ) - (-1) = 2 by ring]; ext; simp
    rw [this]; norm_num
  rwa [heq] at h

lemma subgaussian_weaken {X : TOmega T → ℝ} {c c' : NNReal}
    (h : HasSubgaussianMGF X c (TMeasure T)) (hc : c ≤ c') :
    HasSubgaussianMGF X c' (TMeasure T) where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := by
    refine (h.mgf_le t).trans (Real.exp_le_exp.mpr ?_)
    have : (c:ℝ) ≤ (c':ℝ) := by exact_mod_cast hc
    nlinarith [sq_nonneg t]

/-- Row `i`'s signed sum over the active columns `T`. -/
def rowSum (i : Fin n) (ω : TOmega T) : ℝ := ∑ j : ↥T, A i j.val * tF T j ω

lemma row_subgaussian (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) (i : Fin n) :
    HasSubgaussianMGF (rowSum A T i) (T.card : NNReal) (TMeasure T) := by
  have hindep : iIndepFun (fun j : ↥T => fun ω => A i j.val * tF T j ω) (TMeasure T) := by
    have h0 := tF_indep T
    have h1 := h0.comp (g := fun j : ↥T => fun x : ℝ => A i j.val * x) (fun j => by fun_prop)
    simp only [Function.comp_def] at h1
    exact h1
  have hsub : ∀ j : ↥T, HasSubgaussianMGF (fun ω => A i j.val * tF T j ω)
      (⟨(A i j.val)^2, sq_nonneg _⟩ * 1) (TMeasure T) := by
    intro j
    exact (tF_subgaussian T j).const_mul (A i j.val)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ) hindep (fun j _ => hsub j)
  have hcard : (∑ j : ↥T, (⟨(A i j.val)^2, sq_nonneg (A i j.val)⟩ * 1 : NNReal)) ≤ (T.card : NNReal) := by
    rw [show (T.card : NNReal) = ∑ _j : ↥T, (1:NNReal) by simp]
    apply Finset.sum_le_sum
    intro j _
    show (A i j.val)^2 * 1 ≤ (1:ℝ)
    rcases h01 i j.val with h | h <;> rw [h] <;> norm_num
  have heq : rowSum A T i = fun ω => ∑ j : ↥T, A i j.val * tF T j ω := rfl
  rw [heq]
  exact subgaussian_weaken T hsum hcard

lemma row_tail_bound (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) (i : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    (TMeasure T).real {ω | t ≤ |rowSum A T i ω|} ≤
      2 * Real.exp (-t ^ 2 / (2 * T.card)) := by
  have hsub := row_subgaussian A T h01 i
  set Y : TOmega T → ℝ := rowSum A T i with hY
  have hpos : (TMeasure T).real {ω | t ≤ Y ω} ≤ Real.exp (-t ^ 2 / (2 * T.card)) := by
    have := hsub.measure_ge_le ht
    simpa using this
  have hneg : (TMeasure T).real {ω | t ≤ -Y ω} ≤ Real.exp (-t ^ 2 / (2 * T.card)) := by
    have hsub' := hsub.neg
    have := hsub'.measure_ge_le ht
    simpa using this
  have hsub_eq : {ω | t ≤ |Y ω|} ⊆ {ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rcases abs_cases (Y ω) with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq] at hω; exact Or.inl hω
    · rw [heq] at hω; exact Or.inr hω
  calc (TMeasure T).real {ω | t ≤ |Y ω|}
      ≤ (TMeasure T).real ({ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω}) := measureReal_mono hsub_eq
    _ ≤ (TMeasure T).real {ω | t ≤ Y ω} + (TMeasure T).real {ω | t ≤ -Y ω} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * T.card)) + Real.exp (-t ^ 2 / (2 * T.card)) := add_le_add hpos hneg
    _ = 2 * Real.exp (-t ^ 2 / (2 * T.card)) := by ring

/-- The set of "good" sample points: every row's signed sum stays within `ν * sqrt |T|`. -/
def GoodSet (ν : ℝ) : Finset (TOmega T) :=
  Finset.univ.filter (fun ω => ∀ i : Fin n, |rowSum A T i ω| ≤ ν * Real.sqrt T.card)

lemma goodSet_card_lower_bound (hT : 0 < T.card) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (ν : ℝ) (hν : 0 ≤ ν) :
    (2 : ℝ) ^ T.card * (1 - (n : ℝ) * 2 * Real.exp (-ν ^ 2 / 2))
      ≤ (GoodSet A T ν).card := by
  have hTR : (0:ℝ) < (T.card:ℝ) := by exact_mod_cast hT
  set BadSet : Fin n → Set (TOmega T) :=
    fun i => {ω | ν * Real.sqrt T.card < |rowSum A T i ω|} with hBad_def
  have hbad_bound : ∀ i, (TMeasure T).real (BadSet i) ≤ 2 * Real.exp (-ν ^ 2 / 2) := by
    intro i
    have h := row_tail_bound A T h01 i (ν * Real.sqrt T.card) (by positivity)
    have heqexp : -(ν * Real.sqrt (T.card:ℝ)) ^ 2 / (2 * T.card) = -ν ^ 2 / 2 := by
      rw [mul_pow, Real.sq_sqrt hTR.le]
      field_simp
    have hsub : BadSet i ⊆ {ω | ν * Real.sqrt T.card ≤ |rowSum A T i ω|} := by
      intro ω h
      simp only [hBad_def, Set.mem_ofPred_eq] at h ⊢
      exact le_of_lt h
    calc (TMeasure T).real (BadSet i)
        ≤ (TMeasure T).real {ω | ν * Real.sqrt T.card ≤ |rowSum A T i ω|} :=
          measureReal_mono hsub
      _ ≤ 2 * Real.exp (-ν ^ 2 / 2) := by rwa [heqexp] at h
  have hunion : (TMeasure T).real (⋃ i, BadSet i) ≤ (n : ℝ) * (2 * Real.exp (-ν ^ 2 / 2)) := by
    calc (TMeasure T).real (⋃ i, BadSet i)
        ≤ ∑ i, (TMeasure T).real (BadSet i) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : Fin n, (2 * Real.exp (-ν ^ 2 / 2)) := Finset.sum_le_sum (fun i _ => hbad_bound i)
      _ = (n : ℝ) * (2 * Real.exp (-ν ^ 2 / 2)) := by simp
  have hgood_eq : (↑(GoodSet A T ν) : Set (TOmega T)) = (⋃ i, BadSet i)ᶜ := by
    ext ω
    simp only [GoodSet, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and,
      Set.mem_compl_iff, Set.mem_iUnion, hBad_def, not_exists, not_lt]
  have hmeas : MeasurableSet (⋃ i, BadSet i) := (Set.toFinite _).measurableSet
  have hgood_real : (TMeasure T).real (↑(GoodSet A T ν) : Set (TOmega T))
      = 1 - (TMeasure T).real (⋃ i, BadSet i) := by
    rw [hgood_eq, measureReal_compl hmeas]
    congr 1
    simp [Measure.real, measure_univ]
  have hcard_eq : ((GoodSet A T ν).card : ℝ) / (2 : ℝ) ^ T.card
      = 1 - (TMeasure T).real (⋃ i, BadSet i) := by
    rw [← hgood_real]; exact (TMeasure_real_coe_finset T (GoodSet A T ν)).symm
  have hpow : (0:ℝ) < (2:ℝ) ^ T.card := by positivity
  have hratio : 1 - (n : ℝ) * 2 * Real.exp (-ν ^ 2 / 2)
      ≤ ((GoodSet A T ν).card : ℝ) / (2 : ℝ) ^ T.card := by
    rw [hcard_eq]; linarith [hunion]
  rw [le_div_iff₀ hpow] at hratio
  nlinarith [hratio]

private lemma card_filter_coe (p : Fin n → Prop) [DecidablePred p] :
    ((Finset.univ : Finset ↥T).filter (fun a : ↥T => p a.val)).card = (T.filter p).card := by
  rw [← Finset.attach_eq_univ, Finset.filter_attach, Finset.card_map, Finset.card_attach]

end

end Komlos

open Komlos

theorem solution
    {n : ℕ} (A : Fin n → Fin n → ℝ) (T : Finset (Fin n))
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) (hT : 0 < T.card)
    (s : ℕ) (hs : 2 * s < T.card) (ν : ℝ) (hν : 0 ≤ ν)
    (hbudget : (n : ℝ) * 2 * Real.exp (-ν ^ 2 / 2)
        < 1 - Real.exp (-(T.card : ℝ) * (Real.log 2 - Real.binEntropy ((s : ℝ) / T.card)))) :
    ∃ χ : Fin n → ℝ,
      (∀ j, χ j = 1 ∨ χ j = -1 ∨ χ j = 0) ∧
      (∀ j, j ∉ T → χ j = 0) ∧
      2 * s < (T.filter (fun j => χ j ≠ 0)).card ∧
      (∀ i, |∑ j ∈ T, A i j * χ j| ≤ ν * Real.sqrt T.card) := by
  have hTR : (0:ℝ) < (T.card:ℝ) := by exact_mod_cast hT
  -- Step 1: lower bound on the good set's cardinality.
  have hgood := goodSet_card_lower_bound A T hT h01 ν hν
  -- Step 2: upper bound on the ball volume via the entropy bound.
  have hball := choose_sum_le_exp_mul_binEntropy T.card s hT (by omega)
  -- Step 3: the good set is bigger than the ball, using the budget hypothesis.
  have hbig : (∑ i ∈ Finset.range (s + 1), (T.card.choose i : ℝ)) < (GoodSet A T ν).card := by
    have hkey : Real.exp ((T.card:ℝ) * Real.binEntropy ((s:ℝ)/T.card))
        < (2:ℝ) ^ T.card * (1 - (n:ℝ) * 2 * Real.exp (-ν^2/2)) := by
      have step1 : Real.exp (-(T.card:ℝ) * (Real.log 2 - Real.binEntropy ((s:ℝ)/T.card)))
          < 1 - (n:ℝ) * 2 * Real.exp (-ν^2/2) := by linarith [hbudget]
      have step2 : (2:ℝ)^T.card * Real.exp (-(T.card:ℝ) * (Real.log 2 - Real.binEntropy ((s:ℝ)/T.card)))
          < (2:ℝ)^T.card * (1 - (n:ℝ)*2*Real.exp (-ν^2/2)) :=
        mul_lt_mul_of_pos_left step1 (by positivity)
      calc Real.exp ((T.card:ℝ) * Real.binEntropy ((s:ℝ)/T.card))
          = (2:ℝ)^T.card * Real.exp (-(T.card:ℝ) * (Real.log 2 - Real.binEntropy ((s:ℝ)/T.card))) := by
            rw [show (2:ℝ)^T.card = Real.exp ((T.card:ℝ)*Real.log 2) by
              rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]]
            rw [← Real.exp_add]
            congr 1
            ring
        _ < (2:ℝ)^T.card * (1 - (n:ℝ)*2*Real.exp (-ν^2/2)) := step2
    calc (∑ i ∈ Finset.range (s + 1), (T.card.choose i : ℝ))
        ≤ Real.exp ((T.card:ℝ) * Real.binEntropy ((s:ℝ)/T.card)) := hball
      _ < (2:ℝ) ^ T.card * (1 - (n:ℝ) * 2 * Real.exp (-ν^2/2)) := hkey
      _ ≤ (GoodSet A T ν).card := hgood
  -- Step 4: apply Kleitman's diameter theorem to the good set.
  have hcardι : Fintype.card ↥T = T.card := Fintype.card_coe T
  have hA : (∑ i ∈ Finset.range (s + 1), (Fintype.card ↥T).choose i) < (GoodSet A T ν).card := by
    rw [hcardι]; exact_mod_cast hbig
  have hs' : 2 * s < Fintype.card ↥T := by rw [hcardι]; exact hs
  obtain ⟨x, hxG, y, hyG, hdist⟩ := kleitman_diameter s hs' (GoodSet A T ν) hA
  -- Step 5: build the partial colouring as the difference of x and y.
  simp only [GoodSet, Finset.mem_filter, Finset.mem_univ, true_and] at hxG hyG
  set χ : Fin n → ℝ := fun j => if h : j ∈ T then
      (((if x ⟨j, h⟩ then (1:ℝ) else -1) - (if y ⟨j, h⟩ then (1:ℝ) else -1)) / 2) else 0
    with hχ_def
  have hχ_val : ∀ j (h : j ∈ T),
      χ j = ((if x ⟨j, h⟩ then (1:ℝ) else -1) - (if y ⟨j, h⟩ then (1:ℝ) else -1)) / 2 := by
    intro j h; simp only [hχ_def, dif_pos h]
  have hχ_zero : ∀ j, j ∉ T → χ j = 0 := by
    intro j h; simp only [hχ_def, dif_neg h]
  have hχ_ne_iff : ∀ j (h : j ∈ T), χ j ≠ 0 ↔ x ⟨j, h⟩ ≠ y ⟨j, h⟩ := by
    intro j h
    rw [hχ_val j h]
    cases hxb : x ⟨j, h⟩ <;> cases hyb : y ⟨j, h⟩ <;> norm_num [hxb, hyb]
  refine ⟨χ, ?_, hχ_zero, ?_, ?_⟩
  · intro j
    by_cases h : j ∈ T
    · rw [hχ_val j h]
      cases hxb : x ⟨j, h⟩ <;> cases hyb : y ⟨j, h⟩ <;> norm_num [hxb, hyb]
    · exact Or.inr (Or.inr (hχ_zero j h))
  · have step_a : T.filter (fun j => χ j ≠ 0) = T.filter (fun j => ∃ h : j ∈ T, x ⟨j, h⟩ ≠ y ⟨j, h⟩) := by
      apply Finset.filter_congr
      intro j hj
      rw [hχ_ne_iff j hj]
      exact ⟨fun hne => ⟨hj, hne⟩, fun ⟨h', hne⟩ => hne⟩
    have step_b : ((Finset.univ : Finset ↥T).filter
          (fun a : ↥T => ∃ h : a.val ∈ T, x ⟨a.val, h⟩ ≠ y ⟨a.val, h⟩))
        = (Finset.univ : Finset ↥T).filter (fun a => x a ≠ y a) := by
      apply Finset.filter_congr
      intro a _
      exact ⟨fun ⟨h, hne⟩ => hne, fun hne => ⟨a.property, hne⟩⟩
    have hcard_final : (T.filter (fun j => χ j ≠ 0)).card
        = ((Finset.univ : Finset ↥T).filter (fun a => x a ≠ y a)).card := by
      rw [step_a, ← card_filter_coe T (fun j : Fin n => ∃ h : j ∈ T, x ⟨j, h⟩ ≠ y ⟨j, h⟩), step_b]
    rw [hcard_final]
    exact hdist
  · intro i
    have key : ∀ ω : TOmega T, rowSum A T i ω = ∑ j ∈ T, A i j *
        (if h : j ∈ T then (if ω ⟨j, h⟩ then (1:ℝ) else -1) else 0) := by
      intro ω
      unfold rowSum
      rw [← Finset.sum_attach T (fun j => A i j *
        (if h : j ∈ T then (if ω ⟨j, h⟩ then (1:ℝ) else -1) else 0))]
      apply Finset.sum_congr rfl
      intro a _
      simp only [dif_pos a.property, tF]
    have hxsum := key x
    have hysum := key y
    have hgoal : (∑ j ∈ T, A i j * χ j) = (rowSum A T i x - rowSum A T i y) / 2 := by
      rw [hxsum, hysum, ← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hχ_val j hj, dif_pos hj, dif_pos hj]
      ring
    rw [hgoal]
    have hxb := hxG i
    have hyb := hyG i
    calc |(rowSum A T i x - rowSum A T i y) / 2|
        ≤ (|rowSum A T i x| + |rowSum A T i y|) / 2 := by
          rw [abs_div, abs_two]
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact (abs_sub _ _).trans (by linarith)
      _ ≤ ν * Real.sqrt T.card := by linarith [hxb, hyb]
