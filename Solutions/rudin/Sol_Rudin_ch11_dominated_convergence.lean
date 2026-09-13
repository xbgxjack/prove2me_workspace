import Mathlib
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
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
