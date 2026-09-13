import Mathlib
open Filter Topology Set Real

theorem solution (f : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hone : f 1 = 1) (hrec : ∀ x : ℝ, 0 < x → f (x + 1) = x * f x)
    (hconv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => Real.log (f x))) :
    ∀ x : ℝ, 0 < x → f x = Real.Gamma x := by
  intro x hx
  exact Real.eq_Gamma_of_log_convex hconv (fun {y} hy => hrec y hy) (fun {y} hy => hpos y hy)
    hone hx
