import Mathlib

namespace Erdos287

theorem padic_multiplicity (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (p : ℕ) (hp : Nat.Prime p) (i : ℕ) (hi : i < k) :
    ∃ j, j < k ∧ j ≠ i ∧ padicValNat p (f i) ≤ padicValNat p (f j) := by
  sorry

end Erdos287
