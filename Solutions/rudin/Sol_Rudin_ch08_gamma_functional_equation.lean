import Mathlib
open Filter Topology Set Real Polynomial

theorem solution :
    (∀ x : ℝ, 0 < x → Real.Gamma (x + 1) = x * Real.Gamma x) ∧
    (∀ n : ℕ, Real.Gamma (n + 1) = n.factorial) ∧
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => Real.log (Real.Gamma x)) :=
  ⟨fun _ hx => Real.Gamma_add_one (ne_of_gt hx), Real.Gamma_nat_eq_factorial,
    Real.convexOn_log_Gamma⟩
