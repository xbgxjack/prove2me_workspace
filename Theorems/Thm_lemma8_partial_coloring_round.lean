import Mathlib
import Definitions.Def_RSign
open Finset

theorem lemma8_partial_coloring_round (n : ℕ) {m : ℕ} (a : Fin n → Fin m → ℝ)
    (h01 : ∀ i j, a i j = 0 ∨ a i j = 1) (hm : 1 ≤ m) (lam : ℝ) (hlam : 2 ≤ lam)
    (hbudget : (n:ℝ) * ((12 / Real.log 2) * Real.exp (-lam^2/4)) ≤ (m:ℝ)/10) :
    ∃ x y : Fin m → Bool,
      2 * (m/10) < (Finset.univ.filter (fun j => x j ≠ y j)).card ∧
      ∀ i : Fin n, |∑ j, a i j * ((RSign x j - RSign y j)/2)| ≤ lam * Real.sqrt (m:ℝ) := by sorry
