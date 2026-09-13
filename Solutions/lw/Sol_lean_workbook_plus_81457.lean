import Mathlib
open Real Nat BigOperators

theorem solution : x^2 + y^2 ≥ (1 / 2) * (x + y)^2   := by
  norm_num
