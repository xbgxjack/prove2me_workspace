import Mathlib
import Theorems.Thm_Erdos287_padic_multiplicity

open Finset

private lemma f_le_last {k : ℕ} {f : ℕ → ℕ} (hmono : ∀ i j, i < j → j < k → f i < f j)
    {m : ℕ} (hm : m < k) : f m ≤ f (k - 1) := by
  rcases Nat.lt_or_ge m (k - 1) with h | h
  · exact le_of_lt (hmono m (k - 1) h (by omega))
  · have hmk : m = k - 1 := by omega
    rw [hmk]

private lemma f_ne {k : ℕ} {f : ℕ → ℕ} (hmono : ∀ i j, i < j → j < k → f i < f j)
    {i j : ℕ} (hi : i < k) (hj : j < k) (hij : i ≠ j) : f i ≠ f j := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ne_of_lt (hmono i j h hj)
  · exact ne_of_gt (hmono j i h hi)

/-- If a prime `p` occurs as a denominator and the largest denominator is below `3p`, then `2p`
occurs as a denominator too: `p` and `2p` are the only multiples of `p` available, and the
maximal `p`-adic valuation must be attained twice. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (p : ℕ) (hp : Nat.Prime p) (i : ℕ) (hi : i < k) (hfi : f i = p)
    (hlt : f (k - 1) < 3 * p) :
    ∃ j, j < k ∧ f j = 2 * p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hjk, hjne, hval⟩ := Erdos287.padic_multiplicity k hk f hf1 hsum p hp i hi
  rw [hfi, padicValNat.self hp.one_lt] at hval
  have hj0 : f j ≠ 0 := by have := hf1 j hjk; omega
  have hdvd : p ^ 1 ∣ f j := (padicValNat_dvd_iff_le hj0).mpr hval
  rw [pow_one] at hdvd
  have hne : f j ≠ p := by
    rw [← hfi]
    exact f_ne hmono hjk hi (fun h => hjne h)
  obtain ⟨c, hc⟩ := hdvd
  have hle : f j ≤ f (k - 1) := f_le_last hmono hjk
  have hc2 : c = 2 := by
    rcases Nat.lt_or_ge c 2 with h | h
    · exfalso
      interval_cases c
      · rw [hc] at hj0; simp at hj0
      · rw [hc] at hne; simp at hne
    · rcases Nat.eq_or_lt_of_le h with h2 | h3
      · omega
      · exfalso
        have h3p : 3 * p ≤ p * c := by
          calc 3 * p = p * 3 := by ring
            _ ≤ p * c := by gcongr <;> omega
        omega
  exact ⟨j, hjk, by rw [hc, hc2]; ring⟩
