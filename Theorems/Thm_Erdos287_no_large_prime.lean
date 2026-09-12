import Mathlib

namespace Erdos287

theorem no_large_prime (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (p : ℕ) (hp : Nat.Prime p) (hlt : f (k - 1) < 2 * p) :
    ∀ i, i < k → f i ≠ p := by
  sorry

end Erdos287
