import Mathlib

def RSign {m : ℕ} (χ : Fin m → Bool) (j : Fin m) : ℝ :=
  if χ j then 1 else -1
