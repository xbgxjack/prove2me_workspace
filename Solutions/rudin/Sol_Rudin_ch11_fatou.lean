import Mathlib
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    (∫⁻ x, liminf (fun n => f n x) atTop ∂μ) ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop :=
  lintegral_liminf_le hf
