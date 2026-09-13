import Mathlib
open Filter Topology Set Real Polynomial

theorem solution (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
    (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x) (A : ℝ)
    (hA : deriv f a < A ∧ A < deriv f b) :
    ∃ x ∈ Set.Ioo a b, deriv f x = A := by
  have hf : ∀ x ∈ Set.Icc a b, HasDerivWithinAt f (deriv f x) (Set.Icc a b) x :=
    fun x hx => (hfd x hx).hasDerivAt.hasDerivWithinAt
  obtain ⟨x, hx, hfx⟩ := exists_hasDerivWithinAt_eq_of_gt_of_lt hab.le hf hA.1 hA.2
  exact ⟨x, hx, hfx⟩
