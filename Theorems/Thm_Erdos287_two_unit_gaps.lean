import Mathlib

namespace Erdos287

theorem two_unit_gaps (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2) :
    ∃ i j, i ≠ j ∧ i + 1 < k ∧ j + 1 < k ∧
      f (i + 1) - f i = 1 ∧ f (j + 1) - f j = 1 := by
  sorry

end Erdos287
