import Mathlib
open Real Nat BigOperators

theorem solution : a^4-14*a^2*d^2+49*d^4 ≥ 0 ↔ (a^2-7*d^2)^2 ≥ 0   := by
  norm_num
