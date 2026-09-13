import Mathlib
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

-- ch11_fatou
example {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    (∫⁻ x, liminf (fun n => f n x) atTop ∂μ) ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop :=
  lintegral_liminf_le hf

-- ch11_monotone_convergence
example {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) (hmono : ∀ x, Monotone fun n => f n x)
    (g : X → ℝ≥0∞) (hg : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, g x ∂μ)) :=
  lintegral_tendsto_of_tendsto_of_monotone (fun n => (hf n).aemeasurable)
    (Filter.Eventually.of_forall hmono) (Filter.Eventually.of_forall hg)

-- ch11_measurable_limits
example {X : Type*} [MeasurableSpace X] (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => ⨆ n, f n x) ∧
      Measurable (fun x => limsup (fun n => f n x) atTop) :=
  ⟨Measurable.iSup hf, Measurable.limsup hf⟩

-- ch11_integral_countably_additive
example {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Integrable f μ) (E : ℕ → Set X) (hE : ∀ n, MeasurableSet (E n))
    (hdisj : Pairwise (Function.onFun Disjoint E)) :
    HasSum (fun n => ∫ x in E n, f x ∂μ) (∫ x in ⋃ n, E n, f x ∂μ) :=
  hasSum_integral_iUnion hE hdisj hf.integrableOn

-- ch11_integral_abs_le
example {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ) :
    (Integrable f μ → Integrable (fun x => |f x|) μ ∧ |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ) ∧
    (Measurable f → Integrable g μ → (∀ x, |f x| ≤ g x) → Integrable f μ) := by
  constructor
  · intro hf
    exact ⟨hf.abs, abs_integral_le_integral_abs⟩
  · intro hfm hg hle
    exact Integrable.mono' hg hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using hle x)

-- ch11_dominated_convergence
example {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ) (g h : X → ℝ) (hf : ∀ n, Measurable (f n))
    (hdom : ∀ n, ∀ x, |f n x| ≤ h x) (hh : Integrable h μ)
    (hconv : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Integrable g μ ∧ Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hgm : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hf n).aestronglyMeasurable)
      (Filter.Eventually.of_forall hconv)
  have hgle : ∀ x, ‖g x‖ ≤ h x := by
    intro x
    have := le_of_tendsto_of_tendsto' (Filter.Tendsto.abs (hconv x))
      (tendsto_const_nhds (x := h x) (f := atTop (α := ℕ))) (fun n => hdom n x)
    simpa using this
  have hgi : Integrable g μ :=
    Integrable.mono' hh hgm (Filter.Eventually.of_forall fun x => by simpa using hgle x)
  refine ⟨hgi, ?_⟩
  exact tendsto_integral_of_dominated_convergence h (fun n => (hf n).aestronglyMeasurable) hh
    (fun n => Filter.Eventually.of_forall fun x => by simpa using hdom n x)
    (Filter.Eventually.of_forall hconv)

-- ch09_contraction_principle
example {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (φ : X → X) (c : ℝ) (hc : c < 1) (hc0 : 0 ≤ c)
    (hφ : ∀ x y : X, dist (φ x) (φ y) ≤ c * dist x y) :
    ∃! x : X, φ x = x := by
  have hcoe : ((Real.toNNReal c : ℝ≥0) : ℝ) = c := Real.coe_toNNReal c hc0
  have hlip : LipschitzWith (Real.toNNReal c) φ := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [hcoe]
    exact hφ x y
  have hK : Real.toNNReal c < 1 := by
    rw [← NNReal.coe_lt_coe, hcoe]
    simpa using hc
  have hcw : ContractingWith (Real.toNNReal c) φ := ⟨hK, hlip⟩
  refine ⟨ContractingWith.fixedPoint φ hcw, hcw.fixedPoint_isFixedPt, ?_⟩
  intro y hy
  exact hcw.fixedPoint_unique hy
