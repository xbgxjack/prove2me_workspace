import Mathlib
import Definitions.Def_DiscreteEntropy

open Finset MeasureTheory ProbabilityTheory

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

/-- The shell index, packaged into a fixed-size `Fin` type via a shift and a
(never-triggered, for `Δ ≥ 1/2`) safety `%`. -/
def shellFin (Δ : ℝ) (a : Fin m → ℝ) (ω : Fin m → Bool) : Fin (2*m+3) :=
  ⟨(shellIdx Δ a ω + (m+1)).toNat % (2*m+3), Nat.mod_lt _ (by omega)⟩

/-- Shifted `shellIdx` always lands in `[0, 2m+2]` as an integer, for `Δ ≥ 1/2`. -/
lemma shellIdx_shift_range (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1)
    (hΔ : (1:ℝ)/2 ≤ Δ) (ω : Fin m → Bool) :
    0 ≤ shellIdx Δ a ω + (m+1) ∧ (shellIdx Δ a ω + (m+1)).toNat < 2*m+3 := by
  have hΔpos : 0 < Δ := by linarith
  have hb := shellIdx_bound Δ a h01 hΔpos ω
  rw [Set.mem_Icc] at hb
  have hle : (m:ℝ)/(2*Δ) ≤ m := by
    rw [div_le_iff₀ (by positivity)]
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

lemma shellFin_injOn (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1)
    (hΔ : (1:ℝ)/2 ≤ Δ) {ω ω' : Fin m → Bool}
    (heq : shellFin Δ a ω = shellFin Δ a ω') :
    shellIdx Δ a ω = shellIdx Δ a ω' := by
  have h1 := (shellFin_eq_iff Δ a h01 hΔ ω (shellFin Δ a ω)).mp rfl
  rw [heq] at h1
  have h2 := (shellFin_eq_iff Δ a h01 hΔ ω' (shellFin Δ a ω')).mp rfl
  rw [h1, h2]

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

/-- If `shellIdx = j`, the row sum is at least `2jΔ`. -/
lemma shellIdx_ge (a : Fin m → ℝ) {j : ℤ} (ω : Fin m → Bool) (heq : shellIdx Δ a ω = j)
    (hΔpos : 0 < Δ) : 2 * (j:ℝ) * Δ ≤ rowSumB a ω := by
  unfold shellIdx at heq
  have h1 := Int.floor_le (rowSumB a ω / (2*Δ))
  rw [heq] at h1
  calc 2 * (j:ℝ) * Δ = (j:ℝ) * (2*Δ) := by ring
    _ ≤ (rowSumB a ω / (2*Δ)) * (2*Δ) := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = rowSumB a ω := by field_simp

/-- If `shellIdx = j`, the row sum is less than `2(j+1)Δ`. -/
lemma shellIdx_lt (a : Fin m → ℝ) {j : ℤ} (ω : Fin m → Bool) (heq : shellIdx Δ a ω = j)
    (hΔpos : 0 < Δ) : rowSumB a ω < 2 * ((j:ℝ)+1) * Δ := by
  unfold shellIdx at heq
  have h1 := Int.lt_floor_add_one (rowSumB a ω / (2*Δ))
  rw [heq] at h1
  calc rowSumB a ω = (rowSumB a ω / (2*Δ)) * (2*Δ) := by field_simp
    _ < ((j:ℝ)+1) * (2*Δ) := mul_lt_mul_of_pos_right h1 (by positivity)
    _ = 2 * ((j:ℝ)+1) * Δ := by ring

/-- Tail bound for a positive shell: `Pr[shellIdx = j] ≤ 2·exp(-2j²λ²)` when
`Δ = λ√m` and `j ≥ 1`. -/
lemma shellIdx_prob_le_pos (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1)
    (hΔpos : 0 < Δ) {j : ℤ} (hj : 1 ≤ j) :
    ((univ.filter (fun ω => shellIdx Δ a ω = j)).card : ℝ) / (2:ℝ)^m
      ≤ 2 * Real.exp (-(2*(j:ℝ)*Δ)^2 / (2*m)) := by
  have hjr : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  rw [← uMeasure_real_coe_finset m (univ.filter (fun ω => shellIdx Δ a ω = j))]
  have hsub : (↑(univ.filter (fun ω => shellIdx Δ a ω = j)) : Set (Fin m → Bool))
      ⊆ {ω | 2*(j:ℝ)*Δ ≤ |rowSumB a ω|} := by
    intro ω hω
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
    have hge := shellIdx_ge Δ a ω hω hΔpos
    exact le_trans hge (le_abs_self _)
  calc (uMeasure m).real (↑(univ.filter (fun ω => shellIdx Δ a ω = j)) : Set (Fin m → Bool))
      ≤ (uMeasure m).real {ω | 2*(j:ℝ)*Δ ≤ |rowSumB a ω|} := measureReal_mono hsub
    _ ≤ 2 * Real.exp (-(2*(j:ℝ)*Δ)^2 / (2*m)) :=
        rowSumB_tail_bound m a h01 (2*(j:ℝ)*Δ) (by nlinarith)

/-- Tail bound for a shell two or more below zero:
`Pr[shellIdx = j] ≤ 2·exp(-2(j+1)²λ²)` when `Δ = λ√m` and `j ≤ -2`. -/
lemma shellIdx_prob_le_neg (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1)
    (hΔpos : 0 < Δ) {j : ℤ} (hj : j ≤ -2) :
    ((univ.filter (fun ω => shellIdx Δ a ω = j)).card : ℝ) / (2:ℝ)^m
      ≤ 2 * Real.exp (-(2*((j:ℝ)+1)*Δ)^2 / (2*m)) := by
  have hjr : (j:ℝ) + 1 ≤ -1 := by
    have : (j:ℝ) ≤ -2 := by exact_mod_cast hj
    linarith
  rw [← uMeasure_real_coe_finset m (univ.filter (fun ω => shellIdx Δ a ω = j))]
  have hsub : (↑(univ.filter (fun ω => shellIdx Δ a ω = j)) : Set (Fin m → Bool))
      ⊆ {ω | -(2*((j:ℝ)+1)*Δ) ≤ |rowSumB a ω|} := by
    intro ω hω
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
    have hlt := shellIdx_lt Δ a ω hω hΔpos
    have h2 : -(rowSumB a ω) ≤ |rowSumB a ω| := neg_le_abs _
    linarith
  calc (uMeasure m).real (↑(univ.filter (fun ω => shellIdx Δ a ω = j)) : Set (Fin m → Bool))
      ≤ (uMeasure m).real {ω | -(2*((j:ℝ)+1)*Δ) ≤ |rowSumB a ω|} := measureReal_mono hsub
    _ ≤ 2 * Real.exp (-(2*((j:ℝ)+1)*Δ)^2 / (2*m)) := by
        have := rowSumB_tail_bound m a h01 (-(2*((j:ℝ)+1)*Δ)) (by nlinarith)
        rwa [neg_sq] at this

end
