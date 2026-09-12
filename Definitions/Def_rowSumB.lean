import Mathlib
import Definitions.Def_RSign

def rowSumB {m : ℕ} (a : Fin m → ℝ) (χ : Fin m → Bool) : ℝ :=
  ∑ j, a j * RSign χ j
