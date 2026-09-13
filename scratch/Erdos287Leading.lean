import Mathlib

open Finset

namespace Erdos287

/-- The `p`-adic norm of the reciprocal of a nonzero natural number. -/
private lemma padicNorm_one_div_gen (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m ≠ 0) :
    padicNorm p ((1 : ℚ) / (m : ℚ)) = (p : ℚ) ^ (padicValNat p m : ℤ) := by
  have hm' : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [one_div, padicNorm.eq_zpow_of_nonzero (inv_ne_zero hm'), padicValRat.inv,
    padicValRat.of_nat]
  norm_num

/-- **Cancellation in the leading layer.**  If `1 = 1/f 0 + ⋯ + 1/f (k-1)` and `a ≥ 1` bounds the
`p`-adic valuation of every denominator, then the partial sum over the denominators whose
valuation is *exactly* `a` has `p`-adic norm strictly below `p ^ a`: the leading terms must cancel
against each other. -/
theorem padic_leading_cancel (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (p : ℕ) (hp : Nat.Prime p) (a : ℕ) (ha : 1 ≤ a)
    (hmax : ∀ i, i < k → padicValNat p (f i) ≤ a) :
    padicNorm p (∑ i ∈ (Finset.range k).filter (fun i => padicValNat p (f i) = a),
      (1 : ℚ) / f i) < (p : ℚ) ^ (a : ℤ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.one_lt
  have hpa : (1 : ℚ) < (p : ℚ) ^ (a : ℤ) := by
    calc (1 : ℚ) = (p : ℚ) ^ (0 : ℤ) := by norm_num
      _ < (p : ℚ) ^ (a : ℤ) := by
          refine zpow_lt_zpow_right₀ hp1 ?_
          exact_mod_cast ha
  have hpos : (0 : ℚ) < (p : ℚ) ^ (a : ℤ) := by linarith
  -- split the sum into the leading layer and the rest
  have hsplit :
      (∑ i ∈ (Finset.range k).filter (fun i => padicValNat p (f i) = a), (1 : ℚ) / (f i : ℚ))
        + (∑ i ∈ (Finset.range k).filter (fun i => ¬ (padicValNat p (f i) = a)),
            (1 : ℚ) / (f i : ℚ)) = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact hsum
  -- the rest has strictly smaller norm
  have hRlt : padicNorm p (∑ i ∈ (Finset.range k).filter (fun i => ¬ (padicValNat p (f i) = a)),
      (1 : ℚ) / (f i : ℚ)) < (p : ℚ) ^ (a : ℤ) := by
    refine padicNorm.sum_lt' (fun i hi => ?_) hpos
    have hmem := Finset.mem_filter.mp hi
    have hik : i < k := Finset.mem_range.mp hmem.1
    have hne : padicValNat p (f i) ≠ a := hmem.2
    have hle : padicValNat p (f i) ≤ a := hmax i hik
    rw [padicNorm_one_div_gen p (f i) (by have := hf1 i hik; omega)]
    exact zpow_lt_zpow_right₀ hp1 (by exact_mod_cast (by omega : padicValNat p (f i) < a))
  -- each leading term has norm exactly p ^ a, so the layer sum has norm at most p ^ a
  have hSle : padicNorm p (∑ i ∈ (Finset.range k).filter (fun i => padicValNat p (f i) = a),
      (1 : ℚ) / (f i : ℚ)) ≤ (p : ℚ) ^ (a : ℤ) := by
    refine padicNorm.sum_le' (fun i hi => ?_) (le_of_lt hpos)
    have hmem := Finset.mem_filter.mp hi
    have hik : i < k := Finset.mem_range.mp hmem.1
    rw [padicNorm_one_div_gen p (f i) (by have := hf1 i hik; omega), hmem.2]
  rcases lt_or_eq_of_le hSle with h | h
  · exact h
  exfalso
  have hBS : padicNorm p (∑ i ∈ (Finset.range k).filter (fun i => ¬ (padicValNat p (f i) = a)),
      (1 : ℚ) / (f i : ℚ))
      ≤ padicNorm p (∑ i ∈ (Finset.range k).filter (fun i => padicValNat p (f i) = a),
        (1 : ℚ) / (f i : ℚ)) := by
    rw [h]; exact le_of_lt hRlt
  have hne : padicNorm p (∑ i ∈ (Finset.range k).filter (fun i => padicValNat p (f i) = a),
      (1 : ℚ) / (f i : ℚ))
      ≠ padicNorm p (∑ i ∈ (Finset.range k).filter (fun i => ¬ (padicValNat p (f i) = a)),
        (1 : ℚ) / (f i : ℚ)) := by
    rw [h]; exact fun hh => absurd hh.symm (ne_of_lt hRlt)
  have hmaxeq := padicNorm.add_eq_max_of_ne hne
  rw [hsplit, padicNorm.one, max_eq_left hBS, h] at hmaxeq
  linarith

end Erdos287
