import Mathlib
import Theorems.Thm_Erdos287_no_large_prime

open Finset

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
  have hdvd : 2 ^ (a + 1) ∣ m := by
    obtain ⟨s, hs⟩ : 2 ∣ (t + 1) := by omega
    refine ⟨s, ?_⟩
    have hexp : u + 2 ^ a = 2 ^ a * (t + 1) := by rw [ht]; ring
    rw [hm, hexp, hs]; ring
  have h1 : a + 1 ≤ padicValNat 2 m := (padicValNat_dvd_iff_le hm0).mp hdvd
  have h2 : padicValNat 2 m ≤ a := hmax m hnm hmN
  omega

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
  · obtain ⟨i₁, hi₁k, hi₁dvd⟩ : ∃ i, i < k ∧ 2 ∣ (n + i) := by
      rcases Nat.even_or_odd n with he | ho
      · rw [Nat.even_iff] at he; exact ⟨0, by omega, by omega⟩
      · rw [Nat.odd_iff] at ho; exact ⟨1, by omega, by omega⟩
    have h1 : 1 ≤ padicValNat 2 (n + i₁) :=
      one_le_padicValNat_of_dvd (by omega) hi₁dvd
    exact le_trans h1 (hmax i₁ (Finset.mem_range.mpr hi₁k))
  · intro i hik hine
    rcases lt_or_ge (padicValNat 2 (n + i)) a with h | h
    · exact h
    exfalso
    have hle : padicValNat 2 (n + i) ≤ a := hmax i (Finset.mem_range.mpr hik)
    have heq : padicValNat 2 (n + i) = a := le_antisymm hle h
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

private lemma padicNorm_one_div (m : ℕ) (hm : m ≠ 0) :
    padicNorm 2 ((1 : ℚ) / (m : ℚ)) = (2 : ℚ) ^ (padicValNat 2 m : ℤ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm' : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [one_div, padicNorm.eq_zpow_of_nonzero (inv_ne_zero hm'), padicValRat.inv,
    padicValRat.of_nat]
  norm_num

private lemma one_lt_padicNorm_sum (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    1 < padicNorm 2 (∑ i ∈ Finset.range k, (1 : ℚ) / (n + i)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i₀, hi₀k, ha1, huniq⟩ := exists_unique_max_two_val n k hn hk
  set a := padicValNat 2 (n + i₀) with ha
  have hcast : ∀ i : ℕ, (1 : ℚ) / ((n : ℚ) + (i : ℚ)) = (1 : ℚ) / ((n + i : ℕ) : ℚ) := by
    intro i; push_cast; ring
  rw [Finset.sum_congr rfl (fun i _ => hcast i)]
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

private lemma one_le_two_pow_rat (v : ℕ) : (1 : ℚ) ≤ 2 ^ v := by
  induction v with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; nlinarith

/-- A block of consecutive reciprocals has `2`-adic norm at least `1`. -/
private lemma one_le_padicNorm_block (m t : ℕ) (hm : 0 < m) (ht : 0 < t) :
    1 ≤ padicNorm 2 (∑ j ∈ Finset.range t, (1 : ℚ) / ((m + j : ℕ) : ℚ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge t 2 with h | h
  · have ht1 : t = 1 := by omega
    subst ht1
    rw [Finset.sum_range_one, padicNorm_one_div _ (by omega), zpow_natCast]
    exact one_le_two_pow_rat _
  · have hlt := one_lt_padicNorm_sum m t hm h
    have hb : (∑ i ∈ Finset.range t, (1 : ℚ) / ((m : ℚ) + (i : ℚ)))
        = ∑ j ∈ Finset.range t, (1 : ℚ) / ((m + j : ℕ) : ℚ) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      push_cast; ring
    rw [hb] at hlt
    linarith

/-- **Key new estimate.**  A block of consecutive *even* numbers `2m, 2(m+1), …` contributes a
reciprocal sum of `2`-adic norm `> 1`: halving costs one factor of `2`, and the block itself
has norm `≥ 1`. -/
private lemma one_lt_padicNorm_even_block (m t : ℕ) (hm : 0 < m) (ht : 0 < t) :
    1 < padicNorm 2 (∑ j ∈ Finset.range t, (1 : ℚ) / ((2 * (m + j) : ℕ) : ℚ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (∑ j ∈ Finset.range t, (1 : ℚ) / ((2 * (m + j) : ℕ) : ℚ))
      = (1 : ℚ) / ((2 : ℕ) : ℚ) * ∑ j ∈ Finset.range t, (1 : ℚ) / ((m + j : ℕ) : ℚ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have h0 : ((m + j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast
    field_simp
  have h2 : padicNorm 2 ((1 : ℚ) / ((2 : ℕ) : ℚ)) = 2 := by
    rw [padicNorm_one_div 2 (by norm_num), padicValNat.self (by norm_num)]
    norm_num
  rw [hfac, padicNorm.mul, h2]
  have hb := one_le_padicNorm_block m t hm ht
  linarith

/-- Reciprocals of odd numbers have `2`-adic norm `1`, so any such sum has norm `≤ 1`. -/
private lemma padicNorm_odd_sum_le (s : Finset ℕ) (g : ℕ → ℕ)
    (hodd : ∀ x ∈ s, ¬ 2 ∣ g x) (hg : ∀ x ∈ s, g x ≠ 0) :
    padicNorm 2 (∑ x ∈ s, (1 : ℚ) / (g x : ℚ)) ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine padicNorm.sum_le' (fun x hx => ?_) (by norm_num)
  rw [padicNorm_one_div _ (hg x hx), padicValNat.eq_zero_of_not_dvd (hodd x hx)]
  norm_num

private lemma add_ne_one_of_norms {A B : ℚ} (hA : padicNorm 2 A ≤ 1)
    (hB : 1 < padicNorm 2 B) : A + B ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hne : padicNorm 2 A ≠ padicNorm 2 B := by
    intro hEq; rw [hEq] at hA; linarith
  have hmax := padicNorm.add_eq_max_of_ne (p := 2) hne
  rw [h, padicNorm.one, max_eq_right (by linarith : padicNorm 2 A ≤ padicNorm 2 B)] at hmax
  linarith

/-- An all-odd arithmetic progression of difference `2` cannot have reciprocal sum `1`:
by Bertrand there is a prime in the top half of the range, and it would be a denominator. -/
private lemma no_odd_ap (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hodd : ¬ 2 ∣ f 0)
    (hA : ∀ i, i < k → f i = f 0 + 2 * i)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) : False := by
  have hodd' : f 0 % 2 = 1 := by
    rcases Nat.even_or_odd (f 0) with h | h
    · exact absurd h.two_dvd hodd
    · exact Nat.odd_iff.mp h
  have hf00 : 2 ≤ f 0 := hf1 0 (by omega)
  have hf03 : 3 ≤ f 0 := by omega
  have hf0pos : (0 : ℚ) < (f 0 : ℚ) := by
    have h : 0 < f 0 := by omega
    exact_mod_cast h
  have hstep : ∀ i ∈ Finset.range k, (1 : ℚ) / (f i : ℚ) ≤ 1 / (f 0 : ℚ) := by
    intro i hi
    have hik := Finset.mem_range.mp hi
    have hle : (f 0 : ℚ) ≤ (f i : ℚ) := by
      have h : f 0 ≤ f i := by rw [hA i hik]; omega
      exact_mod_cast h
    exact one_div_le_one_div_of_le hf0pos hle
  have hsum' := Finset.sum_le_sum hstep
  rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum'
  have hk0 : f 0 ≤ k := by
    have h1 : (1 : ℚ) * (f 0 : ℚ) ≤ ((k : ℚ) * (1 / (f 0 : ℚ))) * (f 0 : ℚ) :=
      mul_le_mul_of_nonneg_right hsum' (le_of_lt hf0pos)
    have h2 : ((k : ℚ) * (1 / (f 0 : ℚ))) * (f 0 : ℚ) = (k : ℚ) := by field_simp
    rw [h2, one_mul] at h1
    exact_mod_cast h1
  have hb : f (k - 1) = f 0 + 2 * (k - 1) := hA (k - 1) (by omega)
  obtain ⟨p, hp, hpgt, hple⟩ :=
    Nat.exists_prime_lt_and_le_two_mul ((f (k - 1) - 1) / 2) (by omega)
  have hpodd : p % 2 = 1 := by
    have h2 : p ≠ 2 := by omega
    have h3 := hp.odd_of_ne_two h2
    exact Nat.odd_iff.mp h3
  have hhigh : f (k - 1) < 2 * p := by omega
  have hik : (p - f 0) / 2 < k := by omega
  have hfi : f ((p - f 0) / 2) = p := by
    rw [hA _ hik]
    omega
  exact Erdos287.no_large_prime k hk f hf1 hmono hsum p hp hhigh _ hik hfi

/-- **The 2-adic obstruction for two parity blocks.**  If the denominators consist of one
step-`2` run followed by a second step-`2` run of the opposite parity, the reciprocal sum
cannot be `1`: the even run contributes `2`-adic norm `> 1` and the odd run norm `≤ 1`. -/
private lemma no_two_block (k r : ℕ) (hk : 2 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hA : ∀ i, i < r → f i = f 0 + 2 * i)
    (hB : ∀ i, r ≤ i → i < k → f i = f 0 + 2 * i - 1)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) : False := by
  have hf00 : 2 ≤ f 0 := hf1 0 (by omega)
  have hsplit : (∑ i ∈ Finset.Ico 0 r, (1 : ℚ) / f i)
      + (∑ i ∈ Finset.Ico r k, (1 : ℚ) / f i) = 1 := by
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le r) hrk, ← Finset.range_eq_Ico]
    exact hsum
  by_cases hpar : 2 ∣ f 0
  · obtain ⟨m, hm⟩ := hpar
    have hm1 : 0 < m := by omega
    have hAe : (∑ i ∈ Finset.Ico 0 r, (1 : ℚ) / f i)
        = ∑ j ∈ Finset.range r, (1 : ℚ) / ((2 * (m + j) : ℕ) : ℚ) := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by simp) (fun j hj => ?_)
      have hjr : j < r := Finset.mem_range.mp hj
      have he : f (0 + j) = 2 * (m + j) := by
        have := hA (0 + j) (by omega)
        omega
      rw [he]
    have hBo : padicNorm 2 (∑ i ∈ Finset.Ico r k, (1 : ℚ) / (f i : ℚ)) ≤ 1 := by
      refine padicNorm_odd_sum_le _ f (fun x hx => ?_) (fun x hx => ?_)
      · have h1 := Finset.mem_Ico.mp hx
        have h2 := hB x h1.1 h1.2
        omega
      · have h1 := Finset.mem_Ico.mp hx
        have h2 := hf1 x h1.2
        omega
    rw [hAe] at hsplit
    refine add_ne_one_of_norms hBo (one_lt_padicNorm_even_block m r hm1 (by omega)) ?_
    rw [add_comm]
    exact hsplit
  · rcases Nat.eq_or_lt_of_le hrk with hrk' | hrk'
    · refine no_odd_ap k hk f hf1 hmono hpar (fun i hi => hA i (by omega)) hsum
    · obtain ⟨m, hm⟩ : ∃ m, f 0 = 2 * m + 1 := ⟨f 0 / 2, by omega⟩
      have hBe : (∑ i ∈ Finset.Ico r k, (1 : ℚ) / f i)
          = ∑ j ∈ Finset.range (k - r), (1 : ℚ) / ((2 * ((m + r) + j) : ℕ) : ℚ) := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hjr : j < k - r := Finset.mem_range.mp hj
        have he : f (r + j) = 2 * ((m + r) + j) := by
          have := hB (r + j) (by omega) (by omega)
          omega
        rw [he]
    -- the first run is odd
      have hAo : padicNorm 2 (∑ i ∈ Finset.Ico 0 r, (1 : ℚ) / (f i : ℚ)) ≤ 1 := by
        refine padicNorm_odd_sum_le _ f (fun x hx => ?_) (fun x hx => ?_)
        · have h1 := Finset.mem_Ico.mp hx
          have h2 := hA x h1.2
          omega
        · have h1 := Finset.mem_Ico.mp hx
          have h2 := hf1 x (by omega)
          omega
      rw [hBe] at hsplit
      exact add_ne_one_of_norms hAo
        (one_lt_padicNorm_even_block (m + r) (k - r) (by omega) (by omega)) hsplit

/-- With at most one unit gap the denominators form (at most) two runs of step `2`. -/
private lemma shape (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hgap : ∀ i, i + 1 < k → f (i + 1) = f i + 1 ∨ f (i + 1) = f i + 2)
    (hone : ∀ i j, i + 1 < k → j + 1 < k →
      f (i + 1) = f i + 1 → f (j + 1) = f j + 1 → i = j) :
    ∃ r, 1 ≤ r ∧ r ≤ k ∧ (∀ i, i < r → f i = f 0 + 2 * i) ∧
      (∀ i, r ≤ i → i < k → f i = f 0 + 2 * i - 1) := by
  by_cases hex : ∃ i, i + 1 < k ∧ f (i + 1) = f i + 1
  · obtain ⟨r0, hr0k, hr0⟩ := hex
    have htwo : ∀ i, i + 1 < k → i ≠ r0 → f (i + 1) = f i + 2 := by
      intro i hik hine
      rcases hgap i hik with h | h
      · exact absurd (hone i r0 hik hr0k h hr0) hine
      · exact h
    have hApart : ∀ i, i ≤ r0 → f i = f 0 + 2 * i := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ j ih =>
        intro hi
        have h2 : f (j + 1) = f j + 2 := htwo j (by omega) (by omega)
        have hj := ih (by omega)
        omega
    refine ⟨r0 + 1, by omega, by omega, fun i hi => hApart i (by omega), ?_⟩
    intro i
    induction i with
    | zero => intro h1 h2; omega
    | succ j ih =>
      intro hi hik
      rcases Nat.lt_or_ge r0 j with h | h
      · have h2 : f (j + 1) = f j + 2 := htwo j (by omega) (by omega)
        have hj := ih (by omega) (by omega)
        omega
      · have hjr : j = r0 := by omega
        subst hjr
        have h3 := hApart j (le_refl j)
        omega
  · have htwo : ∀ i, i + 1 < k → f (i + 1) = f i + 2 := by
      intro i hik
      rcases hgap i hik with h | h
      · exact absurd ⟨i, hik, h⟩ hex
      · exact h
    refine ⟨k, by omega, le_refl k, ?_, by intro i h1 h2; omega⟩
    intro i
    induction i with
    | zero => intro _; simp
    | succ j ih =>
      intro hi
      have h2 : f (j + 1) = f j + 2 := htwo j (by omega)
      have hj := ih (by omega)
      omega

/-- **New milestone.**  In any representation `1 = 1/n₁ + ⋯ + 1/n_k` with all consecutive gaps
at most `2`, at least **two** of the gaps are equal to `1`.  Equivalently: a counterexample to
Erdős' problem would need at least three maximal runs of step `2`. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2) :
    ∃ i j, i ≠ j ∧ i + 1 < k ∧ j + 1 < k ∧
      f (i + 1) - f i = 1 ∧ f (j + 1) - f j = 1 := by
  have hgap' : ∀ i, i + 1 < k → f (i + 1) = f i + 1 ∨ f (i + 1) = f i + 2 := by
    intro i hi
    have h1 : f i < f (i + 1) := hmono i (i + 1) (by omega) hi
    have h2 := hgap i hi
    omega
  by_cases hone : ∀ i j, i + 1 < k → j + 1 < k →
      f (i + 1) = f i + 1 → f (j + 1) = f j + 1 → i = j
  · exfalso
    obtain ⟨r, hr1, hrk, hA, hB⟩ := shape k hk f hgap' hone
    exact no_two_block k r hk hr1 hrk f hf1 hmono hA hB hsum
  · push_neg at hone
    obtain ⟨i, j, hi, hj, h1, h2, hne⟩ := hone
    exact ⟨i, j, hne, hi, hj, by omega, by omega⟩
