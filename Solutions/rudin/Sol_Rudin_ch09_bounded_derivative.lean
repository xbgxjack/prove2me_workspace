import Mathlib
open Filter Topology Set Real Polynomial

theorem solution (n m : ℕ) (E : Set (EuclideanSpace ℝ (Fin n))) (hE : IsOpen E)
    (hconv : Convex ℝ E) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (f' : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hf : ∀ x ∈ E, HasFDerivAt f (f' x) x) (M : ℝ) (hM : ∀ x ∈ E, ‖f' x‖ ≤ M) :
    ∀ a ∈ E, ∀ b ∈ E, ‖f b - f a‖ ≤ M * ‖b - a‖ := by
  intro a ha b hb
  exact hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivWithinAt) hM ha hb
