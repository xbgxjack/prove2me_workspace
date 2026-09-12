import Mathlib

open Finset

variable {γ : Type*} [Fintype γ]

theorem gibbs_inequality (p q : γ → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hpq : ∀ x, p x ≠ 0 → q x ≠ 0)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    ∑ x ∈ univ.filter (fun x => p x ≠ 0), p x * Real.log (q x / p x) ≤ 0 := by sorry
