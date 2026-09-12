import Mathlib
import Theorems.Thm_Erdos287_padic_multiplicity

open Finset

/-- Monotone bookkeeping. -/
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

/-- **No large prime denominator.** -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (p : ℕ) (hp : Nat.Prime p) (hlt : f (k - 1) < 2 * p) :
    ∀ i, i < k → f i ≠ p := by
  intro i hi hfi
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
  have hc2 : 2 ≤ c := by
    rcases Nat.lt_or_ge c 2 with h | h
    · exfalso
      interval_cases c
      · rw [hc] at hj0; simp at hj0
      · rw [hc] at hne; simp at hne
    · exact h
  have hle : f j ≤ f (k - 1) := f_le_last hmono hjk
  have h2p : 2 * p ≤ f j := by
    rw [hc]
    calc 2 * p = p * 2 := by ring
      _ ≤ p * c := by gcongr
  omega
