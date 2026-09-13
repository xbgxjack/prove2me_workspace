import Mathlib
open Real Nat BigOperators

theorem solution (a b θ : ℝ) : a * b * (2 * Real.cos θ - 1) * (2 * Real.cos (θ + 1)) / (2 * a * Real.cos θ + b) = a * b * (2 * Real.cos θ - 1) * (2 * Real.cos (θ + 1)) / (2 * a * Real.cos θ + b)   := by
  rfl
