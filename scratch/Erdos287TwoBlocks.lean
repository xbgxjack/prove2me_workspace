import Mathlib

open Finset

namespace Erdos287

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

/-- **Two even runs with different 2-adic weight.**  If two blocks of consecutive even numbers
have reciprocal sums of *different* `2`-adic norm, then those two sums together with any sum of
reciprocals of odd numbers cannot equal `1`. -/
theorem even_blocks_distinct_norm (m₁ t₁ m₂ t₂ : ℕ) (hm₁ : 0 < m₁) (ht₁ : 0 < t₁)
    (hm₂ : 0 < m₂) (ht₂ : 0 < t₂)
    (hdiff : padicNorm 2 (∑ j ∈ Finset.range t₁, (1 : ℚ) / ((2 * (m₁ + j) : ℕ) : ℚ))
           ≠ padicNorm 2 (∑ j ∈ Finset.range t₂, (1 : ℚ) / ((2 * (m₂ + j) : ℕ) : ℚ)))
    (s : Finset ℕ) (g : ℕ → ℕ) (hodd : ∀ x ∈ s, ¬ 2 ∣ g x) (hg : ∀ x ∈ s, g x ≠ 0) :
    (∑ j ∈ Finset.range t₁, (1 : ℚ) / ((2 * (m₁ + j) : ℕ) : ℚ))
      + (∑ j ∈ Finset.range t₂, (1 : ℚ) / ((2 * (m₂ + j) : ℕ) : ℚ))
      + (∑ x ∈ s, (1 : ℚ) / (g x : ℚ)) ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hEq
  set B₁ := ∑ j ∈ Finset.range t₁, (1 : ℚ) / ((2 * (m₁ + j) : ℕ) : ℚ) with hB₁
  set B₂ := ∑ j ∈ Finset.range t₂, (1 : ℚ) / ((2 * (m₂ + j) : ℕ) : ℚ) with hB₂
  set O := ∑ x ∈ s, (1 : ℚ) / (g x : ℚ) with hO
  have h₁ : 1 < padicNorm 2 B₁ := one_lt_padicNorm_even_block m₁ t₁ hm₁ ht₁
  have h₂ : 1 < padicNorm 2 B₂ := one_lt_padicNorm_even_block m₂ t₂ hm₂ ht₂
  have hsum12 : padicNorm 2 (B₁ + B₂) = max (padicNorm 2 B₁) (padicNorm 2 B₂) :=
    padicNorm.add_eq_max_of_ne hdiff
  have hbig : 1 < padicNorm 2 (B₁ + B₂) := by
    rw [hsum12]
    rcases le_total (padicNorm 2 B₁) (padicNorm 2 B₂) with h | h
    · rw [max_eq_right h]; exact h₂
    · rw [max_eq_left h]; exact h₁
  have hOle : padicNorm 2 O ≤ 1 := padicNorm_odd_sum_le s g hodd hg
  have hne : padicNorm 2 O ≠ padicNorm 2 (B₁ + B₂) := by
    intro h; rw [h] at hOle; linarith
  have htot : padicNorm 2 ((B₁ + B₂) + O) = max (padicNorm 2 (B₁ + B₂)) (padicNorm 2 O) :=
    padicNorm.add_eq_max_of_ne (fun h => hne h.symm)
  rw [hEq, padicNorm.one, max_eq_left (by linarith : padicNorm 2 O ≤ padicNorm 2 (B₁ + B₂))] at htot
  linarith

end Erdos287
