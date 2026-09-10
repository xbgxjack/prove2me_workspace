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

end
