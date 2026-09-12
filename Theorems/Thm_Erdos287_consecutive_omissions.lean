import Mathlib

namespace Erdos287

theorem consecutive_omissions (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (x : ℕ) (hx0 : f 0 ≤ x) (hx1 : x + 1 ≤ f (k - 1))
    (hmiss : ∀ i, i < k → f i ≠ x) (hmiss' : ∀ i, i < k → f i ≠ x + 1) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  sorry

end Erdos287
