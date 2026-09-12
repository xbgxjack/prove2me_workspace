import Mathlib
import Theorems.Thm_Erdos287_no_large_prime

open Finset

/-- The largest denominator in a representation of `1` is never prime. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) :
    ¬ Nat.Prime (f (k - 1)) := by
  intro hp
  have h1 : 1 < f (k - 1) := hf1 (k - 1) (by omega)
  exact Erdos287.no_large_prime k hk f hf1 hmono hsum _ hp (by omega) (k - 1) (by omega) rfl
