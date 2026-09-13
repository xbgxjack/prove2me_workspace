import Mathlib
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Integrable f μ) (E : ℕ → Set X) (hE : ∀ n, MeasurableSet (E n))
    (hdisj : Pairwise (Function.onFun Disjoint E)) :
    HasSum (fun n => ∫ x in E n, f x ∂μ) (∫ x in ⋃ n, E n, f x ∂μ) :=
  hasSum_integral_iUnion hE hdisj hf.integrableOn
