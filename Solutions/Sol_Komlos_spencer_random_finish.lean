import Mathlib

open Finset MeasureTheory ProbabilityTheory Real

namespace Komlos

noncomputable section

variable {n : ℕ}

/-- The finite sample space of independent fair coin flips, one per coordinate. -/
abbrev SpOmega (n : ℕ) := Fin n → Bool

/-- The uniform (i.i.d. fair-coin) probability measure on `SpOmega n`. -/
def spMeasure (n : ℕ) : Measure (SpOmega n) :=
  Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)

instance : IsProbabilityMeasure (spMeasure n) := by
  unfold spMeasure; infer_instance

/-- The `j`-th coordinate's Rademacher (±1) random variable. -/
def spF (j : Fin n) (ω : SpOmega n) : ℝ := if ω j then (1:ℝ) else (-1:ℝ)

lemma spF_indep : iIndepFun (fun (j : Fin n) => spF j) (spMeasure n) := by
  have := iIndepFun_pi (μ := fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)
    (X := fun (_ : Fin n) (b : Bool) => if b then (1:ℝ) else (-1:ℝ))
    (fun _ => by fun_prop)
  exact this

lemma spF_meas (j : Fin n) : AEMeasurable (spF j) (spMeasure n) := by
  unfold spF; fun_prop

lemma spF_mem_Icc (j : Fin n) : ∀ᵐ ω ∂(spMeasure n), spF j ω ∈ Set.Icc (-1:ℝ) 1 := by
  filter_upwards with ω
  unfold spF
  split <;> norm_num

lemma spF_integral_eq_zero (j : Fin n) : (spMeasure n)[spF j] = 0 := by
  have key := integral_comp_eval (X := fun _ : Fin n => Bool)
    (μ := fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)
    (f := fun b : Bool => if b = true then (1:ℝ) else (-1:ℝ)) (i := j) (by fun_prop)
  show (∫ ω : SpOmega n, (fun b : Bool => if b = true then (1:ℝ) else (-1:ℝ)) (ω j)
    ∂(spMeasure n)) = 0
  unfold spMeasure
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

lemma spF_subgaussian (j : Fin n) :
    HasSubgaussianMGF (spF j) 1 (spMeasure n) := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := spMeasure n)
    (X := spF j) (a := -1) (b := 1) (spF_meas j) (spF_mem_Icc j) (spF_integral_eq_zero j)
  have heq : (‖(1:ℝ) - (-1)‖₊ / 2) ^ 2 = 1 := by
    have : ‖(1:ℝ) - (-1)‖₊ = 2 := by
      rw [show (1:ℝ) - (-1) = 2 by ring]
      ext
      simp
    rw [this]
    norm_num
  rwa [heq] at h

lemma subgaussian_weaken {X : SpOmega n → ℝ} {c c' : NNReal}
    (h : HasSubgaussianMGF X c (spMeasure n))
    (hc : c ≤ c') : HasSubgaussianMGF X c' (spMeasure n) where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := by
    refine (h.mgf_le t).trans (Real.exp_le_exp.mpr ?_)
    have : (c:ℝ) ≤ (c':ℝ) := by exact_mod_cast hc
    nlinarith [sq_nonneg t]

lemma row_subgaussian (A : Fin n → Fin n → ℝ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (T : Finset (Fin n)) (i : Fin n) :
    HasSubgaussianMGF (fun ω => ∑ j ∈ T, A i j * spF j ω) (T.card : NNReal) (spMeasure n) := by
  have hindep : iIndepFun (fun j : Fin n => fun ω => A i j * spF j ω) (spMeasure n) := by
    have h0 := spF_indep (n := n)
    have h1 := h0.comp (g := fun j : Fin n => fun x : ℝ => A i j * x) (fun j => by fun_prop)
    simp only [Function.comp_def] at h1
    exact h1
  have hsub : ∀ j ∈ T, HasSubgaussianMGF (fun ω => A i j * spF j ω)
      (⟨(A i j)^2, sq_nonneg _⟩ * 1) (spMeasure n) := by
    intro j _
    exact (spF_subgaussian j).const_mul (A i j)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindep hsub
  have hcard : (∑ j ∈ T, (⟨(A i j)^2, sq_nonneg (A i j)⟩ * 1 : NNReal)) ≤ (T.card : NNReal) := by
    rw [show (T.card : NNReal) = ∑ _j ∈ T, (1:NNReal) by simp]
    apply Finset.sum_le_sum
    intro j _
    show (A i j)^2 * 1 ≤ (1:ℝ)
    rcases h01 i j with h | h <;> rw [h] <;> norm_num
  exact subgaussian_weaken hsum hcard

lemma row_tail_bound (A : Fin n → Fin n → ℝ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (T : Finset (Fin n)) (i : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    (spMeasure n).real {ω | t ≤ |∑ j ∈ T, A i j * spF j ω|} ≤
      2 * Real.exp (-t^2 / (2 * T.card)) := by
  have hsub := row_subgaussian A h01 T i
  set Y : SpOmega n → ℝ := fun ω => ∑ j ∈ T, A i j * spF j ω with hY
  have hpos : (spMeasure n).real {ω | t ≤ Y ω} ≤ Real.exp (-t^2 / (2 * T.card)) := by
    have := hsub.measure_ge_le ht
    simpa using this
  have hneg : (spMeasure n).real {ω | t ≤ -Y ω} ≤ Real.exp (-t^2 / (2 * T.card)) := by
    have hsub' := hsub.neg
    have := hsub'.measure_ge_le ht
    simpa using this
  have hsub_eq : {ω | t ≤ |Y ω|} ⊆ {ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rcases abs_cases (Y ω) with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq] at hω; exact Or.inl hω
    · rw [heq] at hω; exact Or.inr hω
  calc (spMeasure n).real {ω | t ≤ |Y ω|}
      ≤ (spMeasure n).real ({ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω}) := by
        apply measureReal_mono hsub_eq
    _ ≤ (spMeasure n).real {ω | t ≤ Y ω} + (spMeasure n).real {ω | t ≤ -Y ω} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-t^2 / (2 * T.card)) + Real.exp (-t^2 / (2 * T.card)) := add_le_add hpos hneg
    _ = 2 * Real.exp (-t^2 / (2 * T.card)) := by ring

lemma exists_good_omega (hn : 0 < n) (A : Fin n → Fin n → ℝ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (T : Finset (Fin n)) (hTpos : 0 < T.card) :
    ∃ ω : SpOmega n, ∀ i,
      |∑ j ∈ T, A i j * spF j ω| ≤ Real.sqrt (2 * (T.card:ℝ) * Real.log (4*n)) := by
  set t : ℝ := Real.sqrt (2 * (T.card:ℝ) * Real.log (4*n)) with ht_def
  have hn4 : (1:ℝ) ≤ 4 * n := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hlog_nonneg : 0 ≤ Real.log (4*n) := Real.log_nonneg hn4
  have hTcard_pos : (0:ℝ) < (T.card:ℝ) := by exact_mod_cast hTpos
  have harg_nonneg : 0 ≤ 2 * (T.card:ℝ) * Real.log (4*n) := by positivity
  have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
  have ht_sq : t^2 = 2 * (T.card:ℝ) * Real.log (4*n) := Real.sq_sqrt harg_nonneg
  have hexp_eq : Real.exp (-t^2 / (2 * T.card)) = 1 / (4*n) := by
    rw [ht_sq]
    rw [show (-(2 * (T.card:ℝ) * Real.log (4*n))) / (2 * T.card) = -Real.log (4*n) by
      field_simp]
    rw [Real.exp_neg, Real.exp_log (by linarith), one_div]
  set Bad : Finset (Fin n) → Fin n → Set (SpOmega n) :=
    fun T i => {ω | t ≤ |∑ j ∈ T, A i j * spF j ω|} with hBad_def
  have hbad_bound : ∀ i, (spMeasure n).real (Bad T i) ≤ 1/(2*n) := by
    intro i
    have := row_tail_bound A h01 T i t ht_nonneg
    rw [hexp_eq] at this
    calc (spMeasure n).real (Bad T i) ≤ 2 * (1/(4*n)) := this
      _ = 1/(2*n) := by ring
  have hunion : (spMeasure n).real (⋃ i, Bad T i) ≤ (n:ℝ) * (1/(2*n)) := by
    calc (spMeasure n).real (⋃ i, Bad T i)
        ≤ ∑ i, (spMeasure n).real (Bad T i) := measureReal_iUnion_fintype_le (fun i => Bad T i)
      _ ≤ ∑ _i : Fin n, (1/(2*n):ℝ) := Finset.sum_le_sum (fun i _ => hbad_bound i)
      _ = (n:ℝ) * (1/(2*n)) := by simp
  have hhalf : (n:ℝ) * (1/(2*n)) = 1/2 := by
    field_simp
  rw [hhalf] at hunion
  have hne : (⋃ i, Bad T i) ≠ Set.univ := by
    intro hcontra
    have huniv1 : (spMeasure n).real (Set.univ : Set (SpOmega n)) = 1 := by
      rw [Measure.real, measure_univ]; simp
    have : (spMeasure n).real (⋃ i, Bad T i) = 1 := by rw [hcontra]; exact huniv1
    rw [this] at hunion
    norm_num at hunion
  obtain ⟨ω, hω⟩ := Set.ne_univ_iff_exists_notMem _ |>.mp hne
  refine ⟨ω, fun i => ?_⟩
  simp only [Set.mem_iUnion, hBad_def, Set.mem_setOf_eq, not_exists, not_le] at hω
  exact le_of_lt (hω i)

end

end Komlos

open Komlos

theorem solution
    (n : ℕ) (hn : 0 < n) (A : Fin n → Fin n → ℝ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (T : Finset (Fin n)) :
    ∃ χ : Fin n → ℝ,
      (∀ j, j ∈ T → (χ j = 1 ∨ χ j = -1)) ∧
      (∀ j, j ∉ T → χ j = 0) ∧
      (∀ i, |∑ j ∈ T, A i j * χ j|
          ≤ Real.sqrt (2 * (T.card : ℝ) * Real.log (4 * n))) := by
  rcases Nat.eq_zero_or_pos T.card with hT0 | hTpos
  · have hTe : T = ∅ := Finset.card_eq_zero.mp hT0
    refine ⟨fun _ => 0, by simp [hTe], by simp, fun i => ?_⟩
    simp [hTe]
  · obtain ⟨ω, hω⟩ := exists_good_omega hn A h01 T hTpos
    refine ⟨fun j => if j ∈ T then spF j ω else 0, ?_, ?_, ?_⟩
    · intro j hj
      simp only [if_pos hj]
      unfold spF
      split <;> simp
    · intro j hj
      simp [hj]
    · intro i
      have heq : ∑ j ∈ T, A i j * (if j ∈ T then spF j ω else 0) = ∑ j ∈ T, A i j * spF j ω := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_pos hj]
      rw [heq]
      exact hω i
