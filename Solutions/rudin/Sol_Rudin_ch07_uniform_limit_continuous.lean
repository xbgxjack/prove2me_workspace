import Mathlib
open MeasureTheory Filter Topology Polynomial
open scoped ENNReal NNReal

theorem solution {X : Type*} [MetricSpace X] (E : Set X) (f : ℕ → X → ℂ)
    (g : X → ℂ) (hcont : ∀ n, ContinuousOn (f n) E) (huc : TendstoUniformlyOn f g atTop E) :
    ContinuousOn g E :=
  huc.continuousOn ((Eventually.of_forall hcont).frequently)
