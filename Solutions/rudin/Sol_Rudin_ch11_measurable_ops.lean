import Mathlib
open MeasureTheory Filter Topology Polynomial
open scoped ENNReal NNReal

theorem solution {X : Type*} [MeasurableSpace X] (f g : X → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => |f x|) ∧ Measurable (fun x => f x + g x) ∧
      Measurable (fun x => f x * g x) :=
  ⟨hf.abs, hf.add hg, hf.mul hg⟩
