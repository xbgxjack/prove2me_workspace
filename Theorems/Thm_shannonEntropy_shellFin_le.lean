import Mathlib
import Definitions.Def_DiscreteEntropy
import Definitions.Def_shellFin
open Finset

theorem shannonEntropy_shellFin_le {m : ℕ} (hm : 1 ≤ m) (a : Fin m → ℝ)
    (h01 : ∀ j, a j = 0 ∨ a j = 1) (lam : ℝ) (hlam : 2 ≤ lam) :
    shannonEntropy (shellFin (lam * Real.sqrt (m:ℝ)) a)
      ≤ (12 / Real.log 2) * Real.exp (-lam^2/4) := by sorry
