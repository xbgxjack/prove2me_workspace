import Mathlib
open Finset

theorem choose_sum_le_exp_mul_binEntropy (n k : ℕ) (hn : 0 < n) (hk2 : 2 * k ≤ n) :
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤ Real.exp (n * Real.binEntropy ((k : ℝ) / n)) := by sorry
