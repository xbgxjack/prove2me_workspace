import Mathlib
open Real Nat BigOperators

theorem solution : ∑ k ∈ Finset.Icc 1 20, k * (k + 1) * (k + 2) = 53130 := by
  decide
