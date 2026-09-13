import Mathlib
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

theorem solution {X : Type*} [MeasurableSpace X] (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => ⨆ n, f n x) ∧
      Measurable (fun x => limsup (fun n => f n x) atTop) :=
  ⟨Measurable.iSup hf, Measurable.limsup hf⟩
