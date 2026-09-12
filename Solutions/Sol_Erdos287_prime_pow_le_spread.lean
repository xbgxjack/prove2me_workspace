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

private lemma first_le_f {k : ℕ} {f : ℕ → ℕ} (hmono : ∀ i j, i < j → j < k → f i < f j)
    {m : ℕ} (hm : m < k) : f 0 ≤ f m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · rw [h]
  · exact le_of_lt (hmono 0 m h hm)

private lemma f_ne {k : ℕ} {f : ℕ → ℕ} (hmono : ∀ i j, i < j → j < k → f i < f j)
    {i j : ℕ} (hi : i < k) (hj : j < k) (hij : i ≠ j) : f i ≠ f j := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ne_of_lt (hmono i j h hj)
  · exact ne_of_gt (hmono j i h hi)

/-- **Prime powers are bounded by the spread of the denominators.** -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (p : ℕ) (hp : Nat.Prime p) (i : ℕ) (hi : i < k) :
    p ^ padicValNat p (f i) ≤ f (k - 1) - f 0 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hjk, hjne, hval⟩ := Erdos287.padic_multiplicity k hk f hf1 hsum p hp i hi
  set a := padicValNat p (f i) with ha
  have hi0 : f i ≠ 0 := by have := hf1 i hi; omega
  have hj0 : f j ≠ 0 := by have := hf1 j hjk; omega
  have hdi : p ^ a ∣ f i := pow_padicValNat_dvd
  have hdj : p ^ a ∣ f j := (padicValNat_dvd_iff_le hj0).mpr hval
  have hlo : f 0 ≤ f i := first_le_f hmono hi
  have hlo' : f 0 ≤ f j := first_le_f hmono hjk
  have hhi : f i ≤ f (k - 1) := f_le_last hmono hi
  have hhi' : f j ≤ f (k - 1) := f_le_last hmono hjk
  have hne : f i ≠ f j := f_ne hmono hi hjk (fun h => hjne h.symm)
  obtain ⟨x, hx⟩ := hdi
  obtain ⟨y, hy⟩ := hdj
  rcases lt_or_gt_of_ne hne with h | h
  · have hxy : x < y := by
      rw [hx, hy] at h
      exact lt_of_mul_lt_mul_left h (Nat.zero_le _)
    have hgap : f i + p ^ a ≤ f j := by
      rw [hx, hy]
      calc p ^ a * x + p ^ a = p ^ a * (x + 1) := by ring
        _ ≤ p ^ a * y := by gcongr; omega
    omega
  · have hxy : y < x := by
      rw [hx, hy] at h
      exact lt_of_mul_lt_mul_left h (Nat.zero_le _)
    have hgap : f j + p ^ a ≤ f i := by
      rw [hx, hy]
      calc p ^ a * y + p ^ a = p ^ a * (y + 1) := by ring
        _ ≤ p ^ a * x := by gcongr; omega
    omega
