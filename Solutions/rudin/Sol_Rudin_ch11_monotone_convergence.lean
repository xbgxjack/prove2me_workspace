import Mathlib
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) (hmono : ∀ x, Monotone fun n => f n x)
    (g : X → ℝ≥0∞) (hg : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, g x ∂μ)) :=
  lintegral_tendsto_of_tendsto_of_monotone (fun n => (hf n).aemeasurable)
    (Filter.Eventually.of_forall hmono) (Filter.Eventually.of_forall hg)
