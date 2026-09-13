import Mathlib
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

theorem solution {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
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
