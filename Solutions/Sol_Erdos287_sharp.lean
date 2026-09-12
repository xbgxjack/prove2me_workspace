import Mathlib

open Finset

/-- **Sharpness of the constant `3` in Erdős Problem 287.** The representation
`1 = 1/2 + 1/3 + 1/6` has gaps `1` and `3`, so every gap is at most `3`: the bound `3`
conjectured in the problem cannot be replaced by `4`. -/
theorem solution :
    ∃ (k : ℕ) (f : ℕ → ℕ), 2 ≤ k ∧ (∀ i, i < k → 1 < f i) ∧
      (∀ i j, i < j → j < k → f i < f j) ∧
      (∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) ∧
      (∀ i, i + 1 < k → f (i + 1) - f i ≤ 3) := by
  refine ⟨3, fun i => if i = 0 then 2 else if i = 1 then 3 else 6, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro i hi; interval_cases i <;> norm_num
  · intro i j hij hj; interval_cases j <;> interval_cases i <;> norm_num
  · norm_num [Finset.sum_range_succ]
  · intro i hi
    have hi2 : i < 2 := by omega
    interval_cases i <;> norm_num
