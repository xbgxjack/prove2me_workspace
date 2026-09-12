import Mathlib

open Finset

namespace Erdos287

/-- If `u < w` both lie in `[n, N]`, `u` has `2`-adic valuation exactly `a`, `w` is divisible
by `2 ^ a`, and no element of `[n, N]` has valuation exceeding `a`, we get a contradiction:
the midpoint-style element `u + 2 ^ a` lies in the interval and has valuation `> a`. -/
private lemma not_lt_of_both_maximal {n N a : ℕ} (hn : 0 < n)
    (hmax : ∀ m, n ≤ m → m ≤ N → padicValNat 2 m ≤ a)
    {u w : ℕ} (hu : n ≤ u) (hwN : w ≤ N)
    (hu_eq : padicValNat 2 u = a) (hw_dvd : 2 ^ a ∣ w) (hlt : u < w) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu0 : u ≠ 0 := by omega
  have hu_dvd : 2 ^ a ∣ u := by
    have := pow_padicValNat_dvd (p := 2) (n := u)
    rwa [hu_eq] at this
  have hu_not : ¬ 2 ^ (a + 1) ∣ u := by
    have := pow_succ_padicValNat_not_dvd (p := 2) hu0
    rwa [hu_eq] at this
  obtain ⟨t, ht⟩ := hu_dvd
  have htodd : ¬ 2 ∣ t := by
    intro h
    obtain ⟨s, hs⟩ := h
    exact hu_not ⟨s, by rw [ht, hs]; ring⟩
  -- the next multiple of `2 ^ a` after `u` still lies at or below `w`
  obtain ⟨y, hy⟩ := hw_dvd
  have hyt : t < y := by
    rw [ht, hy] at hlt
    exact lt_of_mul_lt_mul_left hlt (Nat.zero_le _)
  have hmw : u + 2 ^ a ≤ w := by
    rw [ht, hy]
    calc 2 ^ a * t + 2 ^ a = 2 ^ a * (t + 1) := by ring
      _ ≤ 2 ^ a * y := by gcongr; omega
  set m := u + 2 ^ a with hm
  have hnm : n ≤ m := by omega
  have hmN : m ≤ N := le_trans hmw hwN
  have hm0 : m ≠ 0 := by omega
  -- but `u + 2 ^ a = 2 ^ a * (t + 1)` is divisible by `2 ^ (a + 1)`
  have hdvd : 2 ^ (a + 1) ∣ m := by
    obtain ⟨s, hs⟩ : 2 ∣ (t + 1) := by omega
    refine ⟨s, ?_⟩
    have hexp : u + 2 ^ a = 2 ^ a * (t + 1) := by rw [ht]; ring
    rw [hm, hexp, hs]; ring
  have h1 : a + 1 ≤ padicValNat 2 m := (padicValNat_dvd_iff_le hm0).mp hdvd
  have h2 : padicValNat 2 m ≤ a := hmax m hnm hmN
  omega

/-- Among `k ≥ 2` consecutive positive integers `n, n+1, …, n+k-1` there is a **unique** one of
maximal `2`-adic valuation, and that valuation is positive. -/
private lemma exists_unique_max_two_val (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    ∃ i₀ < k, 1 ≤ padicValNat 2 (n + i₀) ∧
      ∀ i < k, i ≠ i₀ → padicValNat 2 (n + i) < padicValNat 2 (n + i₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i₀, hi₀mem, hmax⟩ :=
    Finset.exists_max_image (Finset.range k) (fun i => padicValNat 2 (n + i))
      ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hi₀k : i₀ < k := Finset.mem_range.mp hi₀mem
  set a := padicValNat 2 (n + i₀) with ha
  refine ⟨i₀, hi₀k, ?_, ?_⟩
  · -- some element of the range is even, so the maximum valuation is at least one
    obtain ⟨i₁, hi₁k, hi₁dvd⟩ : ∃ i, i < k ∧ 2 ∣ (n + i) := by
      rcases Nat.even_or_odd n with he | ho
      · rw [Nat.even_iff] at he; exact ⟨0, by omega, by omega⟩
      · rw [Nat.odd_iff] at ho; exact ⟨1, by omega, by omega⟩
    have h1 : 1 ≤ padicValNat 2 (n + i₁) :=
      one_le_padicValNat_of_dvd (by omega) hi₁dvd
    exact le_trans h1 (hmax i₁ (Finset.mem_range.mpr hi₁k))
  · -- uniqueness of the maximiser
    intro i hik hine
    rcases lt_or_ge (padicValNat 2 (n + i)) a with h | h
    · exact h
    exfalso
    have hle : padicValNat 2 (n + i) ≤ a := hmax i (Finset.mem_range.mpr hik)
    have heq : padicValNat 2 (n + i) = a := le_antisymm hle h
    -- maximality of `a` over the whole interval `[n, n + k - 1]`
    have hmax' : ∀ m, n ≤ m → m ≤ n + k - 1 → padicValNat 2 m ≤ a := by
      intro m hm1 hm2
      have : m - n < k := by omega
      have := hmax (m - n) (Finset.mem_range.mpr this)
      rwa [show n + (m - n) = m by omega] at this
    have hdvd₀ : 2 ^ a ∣ (n + i₀) := by
      have := pow_padicValNat_dvd (p := 2) (n := n + i₀); rwa [← ha] at this
    have hdvdi : 2 ^ a ∣ (n + i) := by
      have := pow_padicValNat_dvd (p := 2) (n := n + i); rwa [heq] at this
    rcases lt_trichotomy (n + i₀) (n + i) with hlt | heqq | hgt
    · exact not_lt_of_both_maximal hn hmax' (by omega) (by omega) ha.symm hdvdi hlt
    · omega
    · exact not_lt_of_both_maximal hn hmax' (by omega) (by omega) heq hdvd₀ hgt

/-- The `2`-adic norm of the reciprocal of a nonzero natural number is `2` raised to its
`2`-adic valuation. -/
private lemma padicNorm_one_div (m : ℕ) (hm : m ≠ 0) :
    padicNorm 2 ((1 : ℚ) / (m : ℚ)) = (2 : ℚ) ^ (padicValNat 2 m : ℤ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm' : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [one_div, padicNorm.eq_zpow_of_nonzero (inv_ne_zero hm'), padicValRat.inv,
    padicValRat.of_nat]
  norm_num

/-- **Key estimate.** For `n ≥ 1` and `k ≥ 2` the `2`-adic norm of
`1/n + 1/(n+1) + … + 1/(n+k-1)` is `2 ^ a > 1`, where `a ≥ 1` is the largest `2`-adic
valuation occurring among the `k` denominators. -/
theorem one_lt_padicNorm_sum (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    1 < padicNorm 2 (∑ i ∈ Finset.range k, (1 : ℚ) / (n + i)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i₀, hi₀k, ha1, huniq⟩ := exists_unique_max_two_val n k hn hk
  set a := padicValNat 2 (n + i₀) with ha
  -- rewrite the summand in a cast-friendly form
  have hcast : ∀ i : ℕ, (1 : ℚ) / ((n : ℚ) + (i : ℚ)) = (1 : ℚ) / ((n + i : ℕ) : ℚ) := by
    intro i; push_cast; ring
  rw [Finset.sum_congr rfl (fun i _ => hcast i)]
  -- split off the unique maximal term
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hi₀k)]
  have hpos : (0 : ℚ) < (2 : ℚ) ^ (a : ℤ) := by positivity
  have hterm : padicNorm 2 ((1 : ℚ) / ((n + i₀ : ℕ) : ℚ)) = (2 : ℚ) ^ (a : ℤ) :=
    padicNorm_one_div _ (by omega)
  have hrest : padicNorm 2 (∑ i ∈ (Finset.range k).erase i₀, (1 : ℚ) / ((n + i : ℕ) : ℚ))
      < (2 : ℚ) ^ (a : ℤ) := by
    refine padicNorm.sum_lt' (fun i hi => ?_) hpos
    have hik : i < k := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
    have hine : i ≠ i₀ := Finset.ne_of_mem_erase hi
    rw [padicNorm_one_div _ (by omega)]
    have : padicValNat 2 (n + i) < a := huniq i hik hine
    exact zpow_lt_zpow_right₀ (by norm_num) (by exact_mod_cast this)
  rw [padicNorm.add_eq_max_of_ne (by rw [hterm]; exact fun h => absurd h.symm (ne_of_lt hrest)),
    hterm, max_eq_left (le_of_lt hrest)]
  calc (1 : ℚ) = (2 : ℚ) ^ (0 : ℤ) := by norm_num
    _ < (2 : ℚ) ^ (a : ℤ) := by
        refine zpow_lt_zpow_right₀ (by norm_num) ?_
        exact_mod_cast ha1

/-- **Erdős (1932).** The sum of the reciprocals of `k ≥ 2` consecutive positive integers is
never an integer. -/
theorem sum_reciprocal_consecutive_not_isInt (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    ¬ (∑ i ∈ Finset.range k, (1 : ℚ) / (n + i)).isInt :=
  padicNorm.not_int_of_not_padic_int 2 (one_lt_padicNorm_sum n k hn hk)

/-- In particular, the sum of the reciprocals of `k ≥ 2` consecutive positive integers is
never equal to `1`. -/
theorem sum_reciprocal_consecutive_ne_one (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    ∑ i ∈ Finset.range k, (1 : ℚ) / (n + i) ≠ 1 := by
  intro h
  exact sum_reciprocal_consecutive_not_isInt n k hn hk (by rw [h]; decide)

end Erdos287

namespace Erdos287

/-- **Milestone (the gap-two bound).** For every representation of `1` as a sum of `k ≥ 2`
reciprocals of strictly increasing integers `> 1`, some consecutive gap is at least `2`.
This is the `≥ 2` case of Erdős' problem, equivalent to the 1932 result above. -/
theorem exists_gap_two (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) :
    ∃ i, i + 1 < k ∧ 2 ≤ f (i + 1) - f i := by
  by_contra hcon
  push_neg at hcon
  have hstep : ∀ i, i + 1 < k → f (i + 1) = f i + 1 := by
    intro i hi
    have h1 : f i < f (i + 1) := hmono i (i + 1) (by omega) hi
    have h2 : f (i + 1) - f i < 2 := hcon i hi
    omega
  have hform : ∀ i, i < k → f i = f 0 + i := by
    intro i hi
    induction i with
    | zero => simp
    | succ j ih =>
      have hj : j < k := by omega
      rw [hstep j (by omega), ih hj]
      omega
  have hrw : ∑ i ∈ Finset.range k, (1 : ℚ) / f i
      = ∑ i ∈ Finset.range k, (1 : ℚ) / ((f 0 : ℚ) + (i : ℚ)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hform i (Finset.mem_range.mp hi)]
    push_cast; ring
  rw [hrw] at hsum
  have hf0 : 0 < f 0 := by have := hf1 0 (by omega); omega
  exact sum_reciprocal_consecutive_ne_one (f 0) k hf0 hk hsum

/-- **Sharpness.** `1 = 1/2 + 1/3 + 1/6` is a representation all of whose gaps are at most `3`,
so the bound `3` in Erdős' problem cannot be improved. -/
theorem gap_three_is_sharp :
    ∃ (k : ℕ) (f : ℕ → ℕ), 2 ≤ k ∧ (∀ i, i < k → 1 < f i) ∧
      (∀ i j, i < j → j < k → f i < f j) ∧
      (∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) ∧
      (∀ i, i + 1 < k → f (i + 1) - f i ≤ 3) := by
  refine ⟨3, fun i => if i = 0 then 2 else if i = 1 then 3 else 6, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro i hi; interval_cases i <;> norm_num
  · intro i j hij hj; interval_cases j <;> interval_cases i <;> norm_num
  · norm_num [Finset.sum_range_succ]
  · intro i hi
    have hi2 : i < 2 := by omega
    interval_cases i <;> norm_num

end Erdos287
