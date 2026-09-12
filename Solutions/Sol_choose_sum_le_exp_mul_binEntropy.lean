import Mathlib

open Finset

noncomputable section

theorem solution (n k : ℕ) (hn : 0 < n) (hk2 : 2 * k ≤ n) :
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤ Real.exp (n * Real.binEntropy ((k : ℝ) / n)) := by
  set lam : ℝ := (k : ℝ) / n with hlam_def
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlam0 : 0 ≤ lam := by positivity
  have h2k : (2:ℝ) * (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast hk2
  have hnlam0 : (n : ℝ) * lam = k := by rw [hlam_def]; field_simp
  have hlam1 : lam ≤ 1 - lam := by nlinarith [hnlam0, hnR]
  have h1lam_nonneg0 : (0:ℝ) ≤ 1 - lam := by linarith
  -- key pointwise inequality: for j ≤ k, lam^k * (1-lam)^(n-k) ≤ lam^j * (1-lam)^(n-j)
  have hkey : ∀ j ≤ k, lam ^ k * (1 - lam) ^ (n - k) ≤ lam ^ j * (1 - lam) ^ (n - j) := by
    intro j hjk
    have hnk : n - j = (n - k) + (k - j) := by omega
    rw [hnk, pow_add]
    have hle : lam ^ (k - j) ≤ (1 - lam) ^ (k - j) := pow_le_pow_left₀ hlam0 hlam1 _
    calc lam ^ k * (1 - lam) ^ (n - k)
        = lam ^ j * lam ^ (k - j) * (1 - lam) ^ (n - k) := by
          rw [← pow_add]; congr 2; omega
      _ ≤ lam ^ j * (1 - lam) ^ (k - j) * (1 - lam) ^ (n - k) := by
          have h1lam_nonneg : (0:ℝ) ≤ 1 - lam := by linarith
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = lam ^ j * ((1 - lam) ^ (n - k) * (1 - lam) ^ (k - j)) := by ring
  have hstep : ∀ j ∈ Finset.range (k + 1),
      (n.choose j : ℝ) * (lam ^ k * (1 - lam) ^ (n - k))
        ≤ (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j)) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    exact mul_le_mul_of_nonneg_left (hkey j (by omega)) (by positivity)
  have hsumC : (∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ)) * (lam ^ k * (1 - lam) ^ (n - k))
      ≤ ∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hstep
  have hsum2 : ∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j))
      ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_subset_range.mpr (by omega)
    · intro j _ _
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (pow_nonneg h1lam_nonneg0 _))
  have hbin : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j)) = 1 := by
    have hap := add_pow lam (1 - lam) n
    simp only [add_sub_cancel, one_pow] at hap
    have hreindex : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j))
        = ∑ m ∈ Finset.range (n + 1), lam ^ m * (1 - lam) ^ (n - m) * (n.choose m : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _; ring
    rw [hreindex, ← hap]
  have hfinal : (∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ)) * (lam ^ k * (1 - lam) ^ (n - k)) ≤ 1 := by
    calc (∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ)) * (lam ^ k * (1 - lam) ^ (n - k))
        ≤ ∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j)) := hsumC
      _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (lam ^ j * (1 - lam) ^ (n - j)) := hsum2
      _ = 1 := hbin
  rcases eq_or_lt_of_le hlam0 with hlam0' | hlam0'
  · -- lam = 0, i.e. k = 0
    have hk0 : k = 0 := by
      by_contra hk0'
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0'
      have hlampos : (0:ℝ) < lam := by rw [hlam_def]; positivity
      linarith [hlam0']
    subst hk0
    simp only [hlam_def, Nat.cast_zero, zero_div, Real.binEntropy_zero, mul_zero, Real.exp_zero]
    norm_num
  · have hlam1' : lam < 1 := by linarith
    have hpos : 0 < lam ^ k * (1 - lam) ^ (n - k) := by positivity
    have hdiv : (∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ)) ≤ 1 / (lam ^ k * (1 - lam) ^ (n - k)) := by
      rw [le_div_iff₀ hpos]
      exact hfinal
    refine hdiv.trans (le_of_eq ?_)
    have hkn : k ≤ n := by omega
    have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by push_cast [hkn]; ring
    have hnlam : (n : ℝ) * lam = k := by rw [hlam_def]; field_simp
    have hn1lam : (n : ℝ) * (1 - lam) = (n : ℝ) - k := by
      rw [hlam_def]; field_simp
    have h1lam_pos : (0:ℝ) < 1 - lam := by linarith
    have hRHSpos : (0:ℝ) < lam⁻¹ ^ k * (1 - lam)⁻¹ ^ (n - k) := by positivity
    have hlogRHS : Real.log (lam⁻¹ ^ k * (1 - lam)⁻¹ ^ (n - k))
        = (n : ℝ) * Real.binEntropy lam := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        Real.log_inv, Real.log_inv, hcast, Real.binEntropy, Real.log_inv, Real.log_inv]
      linear_combination (Real.log lam - Real.log (1 - lam)) * hnlam
    rw [← hlogRHS, Real.exp_log hRHSpos, one_div, mul_inv, inv_pow, inv_pow]

end
