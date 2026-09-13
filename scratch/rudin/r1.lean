import Mathlib
open MeasureTheory Filter Topology Polynomial
open scoped ENNReal NNReal

-- ch11_measurable_ops
example {X : Type*} [MeasurableSpace X] (f g : X → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => |f x|) ∧ Measurable (fun x => f x + g x) ∧
      Measurable (fun x => f x * g x) :=
  ⟨hf.abs, hf.add hg, hf.mul hg⟩

-- ch11_series_integral
example {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    (∫⁻ x, ∑' n, f n x ∂μ) = ∑' n, ∫⁻ x, f n x ∂μ :=
  lintegral_tsum fun n => (hf n).aemeasurable

-- ch07_uniform_limit_continuous
example {X : Type*} [MetricSpace X] (E : Set X) (f : ℕ → X → ℂ)
    (g : X → ℂ) (hcont : ∀ n, ContinuousOn (f n) E) (huc : TendstoUniformlyOn f g atTop E) :
    ContinuousOn g E :=
  huc.continuousOn ((Eventually.of_forall hcont).frequently)

-- ch08_fundamental_theorem_of_algebra
example (n : ℕ) (hn : 1 ≤ n) (a : ℕ → ℂ) (han : a n ≠ 0) :
    ∃ z : ℂ, ∑ k ∈ Finset.range (n + 1), a k * z ^ k = 0 := by
  set p : ℂ[X] := ∑ k ∈ Finset.range (n + 1), C (a k) * X ^ k with hp
  have hdeg_le : p.degree ≤ (n : WithBot ℕ) := by
    rw [hp]
    refine le_trans (degree_sum_le _ _) ?_
    simp only [Finset.sup_le_iff, Finset.mem_range]
    intro k hk
    calc (C (a k) * X ^ k).degree ≤ (C (a k)).degree + (X ^ k : ℂ[X]).degree :=
          degree_mul_le _ _
      _ ≤ 0 + (k : WithBot ℕ) := add_le_add degree_C_le (degree_X_pow_le k)
      _ = (k : WithBot ℕ) := by simp
      _ ≤ (n : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_iff.mp hk
  have hcoeff : p.coeff n = a n := by
    rw [hp, finsetSum_coeff]
    rw [Finset.sum_eq_single n]
    · simp
    · intro k _ hkn
      have hnk : (n : ℕ) ≠ k := fun h => hkn h.symm
      simp [coeff_C_mul, coeff_X_pow, hnk]
    · intro h
      exact absurd (Finset.self_mem_range_succ n) h
  have hdeg : p.degree = (n : WithBot ℕ) :=
    degree_eq_of_le_of_coeff_ne_zero hdeg_le (by rw [hcoeff]; exact han)
  have hpos : 0 < p.degree := by
    rw [hdeg]; exact_mod_cast hn
  obtain ⟨z, hz⟩ := Complex.exists_root hpos
  refine ⟨z, ?_⟩
  have h2 := hz
  rw [IsRoot, hp, eval_finsetSum] at h2
  simpa using h2
