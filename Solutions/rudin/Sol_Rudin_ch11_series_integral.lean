import Mathlib
open MeasureTheory Filter Topology Polynomial
open scoped ENNReal NNReal

theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    (∫⁻ x, ∑' n, f n x ∂μ) = ∑' n, ∫⁻ x, f n x ∂μ :=
  lintegral_tsum fun n => (hf n).aemeasurable
