import Mathlib

open Finset

/-- The `p`-adic norm of the reciprocal of a nonzero natural number. -/
private lemma padicNorm_one_div_gen (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m ≠ 0) :
    padicNorm p ((1 : ℚ) / (m : ℚ)) = (p : ℚ) ^ (padicValNat p m : ℤ) := by
  have hm' : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [one_div, padicNorm.eq_zpow_of_nonzero (inv_ne_zero hm'), padicValRat.inv,
    padicValRat.of_nat]
  norm_num

/-- **Multiplicity of the maximal valuation.**  For every prime `p` and every index `i` there is
a different index whose denominator is at least as divisible by `p`. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (p : ℕ) (hp : Nat.Prime p) (i : ℕ) (hi : i < k) :
    ∃ j, j < k ∧ j ≠ i ∧ padicValNat p (f i) ≤ padicValNat p (f j) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j₀, hj₀k, hj₀ne⟩ : ∃ j, j < k ∧ j ≠ i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨0, by omega, by omega⟩
  by_contra hcon
  push_neg at hcon
  set a := padicValNat p (f i) with ha
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.one_lt
  have hpos : (0 : ℚ) < (p : ℚ) ^ (a : ℤ) := by
    have h0 : (0 : ℚ) < (p : ℚ) := by linarith
    positivity
  have hterm : padicNorm p ((1 : ℚ) / (f i : ℚ)) = (p : ℚ) ^ (a : ℤ) :=
    padicNorm_one_div_gen p (f i) (by have := hf1 i hi; omega)
  have hrest : padicNorm p (∑ j ∈ (Finset.range k).erase i, (1 : ℚ) / (f j : ℚ))
      < (p : ℚ) ^ (a : ℤ) := by
    refine padicNorm.sum_lt' (fun j hj => ?_) hpos
    have hjk : j < k := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
    have hjne : j ≠ i := Finset.ne_of_mem_erase hj
    rw [padicNorm_one_div_gen p (f j) (by have := hf1 j hjk; omega)]
    exact zpow_lt_zpow_right₀ hp1 (by exact_mod_cast hcon j hjk hjne)
  have hsplit : padicNorm p (1 : ℚ) = (p : ℚ) ^ (a : ℤ) := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hi),
      padicNorm.add_eq_max_of_ne (by rw [hterm]; exact fun h => absurd h.symm (ne_of_lt hrest)),
      hterm, max_eq_left (le_of_lt hrest)]
  rw [padicNorm.one] at hsplit
  have ha0 : a = 0 := by
    by_contra h
    have h1 : (1 : ℚ) < (p : ℚ) ^ (a : ℤ) := by
      calc (1 : ℚ) = (p : ℚ) ^ (0 : ℤ) := by norm_num
        _ < (p : ℚ) ^ (a : ℤ) := by
            refine zpow_lt_zpow_right₀ hp1 ?_
            exact_mod_cast Nat.pos_of_ne_zero h
    rw [← hsplit] at h1
    exact absurd h1 (by norm_num)
  have := hcon j₀ hj₀k hj₀ne
  omega
