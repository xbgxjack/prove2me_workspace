import Mathlib
import Theorems.Thm_Erdos287_padic_multiplicity
import Theorems.Thm_Erdos287_no_large_prime

open Finset

namespace Erdos287

/-! ### Helpers (same as in the earlier files) -/

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

/-! ### 1. The bridge: two consecutive omissions force a gap of three -/

/-- If two consecutive integers inside the range of the denominators are both missing from the
list, then some consecutive gap is at least `3`. -/
theorem consecutive_omissions (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (x : ℕ) (hx0 : f 0 ≤ x) (hx1 : x + 1 ≤ f (k - 1))
    (hmiss : ∀ i, i < k → f i ≠ x) (hmiss' : ∀ i, i < k → f i ≠ x + 1) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  classical
  set A : Finset ℕ := (Finset.range k).filter (fun j => f j < x) with hA
  have h0A : 0 ∈ A := by
    rw [hA, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, lt_of_le_of_ne hx0 (hmiss 0 (by omega))⟩
  have hne : A.Nonempty := ⟨0, h0A⟩
  set i := A.max' hne with hi
  have hiA : i ∈ A := A.max'_mem hne
  have hmem := Finset.mem_filter.mp hiA
  have hik : i < k := Finset.mem_range.mp hmem.1
  have hfi : f i < x := hmem.2
  have hlast : k - 1 ∉ A := by
    intro h
    have := (Finset.mem_filter.mp h).2
    omega
  have hik1 : i + 1 < k := by
    rcases Nat.lt_or_ge i (k - 1) with h | h
    · omega
    · exfalso
      apply hlast
      have hik' : i = k - 1 := by omega
      rwa [hik'] at hiA
  have hnext : ¬ (f (i + 1) < x) := by
    intro h
    have hmemA : i + 1 ∈ A := by
      rw [hA, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, h⟩
    have := A.le_max' _ hmemA
    omega
  have h1 : f (i + 1) ≠ x := hmiss _ hik1
  have h2 : f (i + 1) ≠ x + 1 := hmiss' _ hik1
  exact ⟨i, hik1, by omega⟩

/-! ### 2. A prime denominator forces its double -/

/-- If a prime `p` occurs as a denominator and the largest denominator is below `3p`, then `2p`
occurs as a denominator too: `p` and `2p` are the only multiples of `p` available, and the
maximal `p`-adic valuation must be attained twice. -/
theorem prime_forces_double (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (p : ℕ) (hp : Nat.Prime p) (i : ℕ) (hi : i < k) (hfi : f i = p)
    (hlt : f (k - 1) < 3 * p) :
    ∃ j, j < k ∧ f j = 2 * p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hjk, hjne, hval⟩ := padic_multiplicity k hk f hf1 hsum p hp i hi
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

/-! ### 3. Primes in the top half are flanked by denominators -/

/-- In a representation with all gaps at most `2`, every prime `p` past half the range is
missing from the denominators, hence both its neighbours `p - 1` and `p + 1` are denominators —
so `p` sits strictly inside a run of even denominators. -/
theorem prime_neighbours (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (p : ℕ) (hp : Nat.Prime p) (hlo : f 0 < p) (hhi : p + 1 ≤ f (k - 1))
    (h2 : f (k - 1) < 2 * p) :
    (∃ i, i < k ∧ f i = p - 1) ∧ (∃ j, j < k ∧ f j = p + 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpmiss : ∀ i, i < k → f i ≠ p := no_large_prime k hk f hf1 hmono hsum p hp h2
  constructor
  · by_contra hcon
    push_neg at hcon
    obtain ⟨i, hik, hgap3⟩ :=
      consecutive_omissions k hk f hmono (p - 1) (by omega) (by omega)
        (fun i hi => hcon i hi) (fun i hi => by rw [show p - 1 + 1 = p by omega]; exact hpmiss i hi)
    have := hgap i hik
    omega
  · by_contra hcon
    push_neg at hcon
    obtain ⟨i, hik, hgap3⟩ :=
      consecutive_omissions k hk f hmono p (by omega) (by omega)
        (fun i hi => hpmiss i hi) (fun i hi => hcon i hi)
    have := hgap i hik
    omega

end Erdos287
