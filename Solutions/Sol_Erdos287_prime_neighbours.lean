import Mathlib
import Theorems.Thm_Erdos287_no_large_prime
import Theorems.Thm_Erdos287_consecutive_omissions

open Finset

/-- In a representation with all gaps at most `2`, every prime `p` past half the range is
missing from the denominators, hence both its neighbours `p - 1` and `p + 1` are denominators —
so `p` sits strictly inside a run of even denominators. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (p : ℕ) (hp : Nat.Prime p) (hlo : f 0 < p) (hhi : p + 1 ≤ f (k - 1))
    (h2 : f (k - 1) < 2 * p) :
    (∃ i, i < k ∧ f i = p - 1) ∧ (∃ j, j < k ∧ f j = p + 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpmiss : ∀ i, i < k → f i ≠ p := Erdos287.no_large_prime k hk f hf1 hmono hsum p hp h2
  constructor
  · by_contra hcon
    push_neg at hcon
    obtain ⟨i, hik, hgap3⟩ :=
      Erdos287.consecutive_omissions k hk f hmono (p - 1) (by omega) (by omega)
        (fun i hi => hcon i hi) (fun i hi => by rw [show p - 1 + 1 = p by omega]; exact hpmiss i hi)
    have := hgap i hik
    omega
  · by_contra hcon
    push_neg at hcon
    obtain ⟨i, hik, hgap3⟩ :=
      Erdos287.consecutive_omissions k hk f hmono p (by omega) (by omega)
        (fun i hi => hpmiss i hi) (fun i hi => hcon i hi)
    have := hgap i hik
    omega
