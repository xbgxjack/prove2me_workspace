import Mathlib
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ) :
    (Integrable f μ → Integrable (fun x => |f x|) μ ∧ |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ) ∧
    (Measurable f → Integrable g μ → (∀ x, |f x| ≤ g x) → Integrable f μ) := by
  constructor
  · intro hf
    exact ⟨hf.abs, abs_integral_le_integral_abs⟩
  · intro hfm hg hle
    exact Integrable.mono' hg hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using hle x)
