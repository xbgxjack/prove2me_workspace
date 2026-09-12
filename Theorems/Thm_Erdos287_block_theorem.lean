import Mathlib

namespace Erdos287

theorem block_theorem (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    ¬ ∃ m : ℤ, (∑ i ∈ Finset.range k, (1 : ℚ) / (n + i)) = (m : ℚ) := by
  sorry

end Erdos287
