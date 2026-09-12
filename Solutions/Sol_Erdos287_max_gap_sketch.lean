import Mathlib
import Theorems.Thm_Erdos287_two_unit_gaps
import Theorems.Thm_Erdos287_mixed_gap_core

open Finset

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  by_contra hcon
  push_neg at hcon
  have hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2 := by
    intro i hi
    have := hcon i hi
    omega
  exact Erdos287.mixed_gap_core k hk f hf1 hmono hsum hgap
    (Erdos287.two_unit_gaps k hk f hf1 hmono hsum hgap)
