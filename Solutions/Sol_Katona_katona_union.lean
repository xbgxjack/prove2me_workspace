import Mathlib
import Definitions.Def_TIntersecting
import Definitions.Def_katonaBound

open Finset UV
open scoped FinsetFamily

namespace Katona

variable {n : ℕ}

/-- The shift predicate: `a` genuinely moves under `cpr z i`. -/
@[reducible] def Shifts (z i : Fin n) (a : Finset (Fin n)) : Prop := z ∉ a ∧ i ∈ a

noncomputable def cpr (z i : Fin n) (a : Finset (Fin n)) : Finset (Fin n) :=
  UV.compress ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) a

lemma compress_singleton_eq (z i : Fin n) (hzi : z ≠ i) (a : Finset (Fin n)) :
    cpr z i a = if Shifts z i a then insert z (a.erase i) else a := by
  unfold cpr UV.compress Shifts
  by_cases h : Disjoint ({z} : Finset (Fin n)) a ∧ ({i} : Finset (Fin n)) ≤ a
  · have hz : z ∉ a := Finset.disjoint_singleton_left.mp h.1
    have hi : i ∈ a := Finset.singleton_subset_iff.mp h.2
    rw [if_pos h, if_pos ⟨hz, hi⟩]
    ext x
    simp only [Finset.mem_sdiff, Finset.sup_eq_union, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hx1, hx2⟩
      rcases hx1 with hxa | rfl
      · exact Or.inr ⟨hx2, hxa⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨hx2, hxa⟩)
      · exact ⟨Or.inr rfl, hzi⟩
      · exact ⟨Or.inl hxa, hx2⟩
  · have h' : ¬ (z ∉ a ∧ i ∈ a) := by
      rintro ⟨hz, hi⟩
      exact h ⟨Finset.disjoint_singleton_left.mpr hz, Finset.singleton_subset_iff.mpr hi⟩
    rw [if_neg h, if_neg h']

/-- F1: if neither set shifts, `cpr` fixes both, so the intersection is unchanged. -/
lemma inter_of_not_shifts (z i : Fin n) (hzi : z ≠ i) {a b : Finset (Fin n)}
    (ha : ¬ Shifts z i a) (hb : ¬ Shifts z i b) : cpr z i a ∩ cpr z i b = a ∩ b := by
  rw [compress_singleton_eq z i hzi a, compress_singleton_eq z i hzi b, if_neg ha, if_neg hb]

/-- F2: shifting one side while the other is fixed never decreases the intersection size. -/
lemma card_le_card_compress_inter (z i : Fin n) (hzi : z ≠ i) {a b : Finset (Fin n)}
    (ha : Shifts z i a) (hb : ¬ Shifts z i b) : (a ∩ b).card ≤ (cpr z i a ∩ b).card := by
  rw [compress_singleton_eq z i hzi a, if_pos ha]
  obtain ⟨haz, hai⟩ := ha
  simp only [Shifts, not_and_or, not_not] at hb
  by_cases hzb : z ∈ b
  · -- z ∈ b: the shift may gain z while losing at most `i`, so the size cannot drop.
    have heq : insert z (a.erase i) ∩ b = insert z ((a ∩ b).erase i) := by
      rw [← Finset.erase_inter i a b]
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxb⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, hxb⟩
      · rintro (rfl | ⟨hx, hxb⟩)
        · exact ⟨Or.inl rfl, hzb⟩
        · exact ⟨Or.inr hx, hxb⟩
    rw [heq]
    have hznotin : z ∉ (a ∩ b).erase i := by
      simp only [Finset.mem_erase, Finset.mem_inter]
      tauto
    rw [Finset.card_insert_of_notMem hznotin]
    by_cases hiab : i ∈ a ∩ b
    · rw [Finset.card_erase_of_mem hiab]
      have : 0 < (a ∩ b).card := Finset.card_pos.mpr ⟨i, hiab⟩
      omega
    · rw [Finset.erase_eq_of_notMem hiab]
      omega
  · -- z ∉ b, so ¬Shifts b forces i ∉ b, hence i ∉ a ∩ b and erasing does nothing.
    have hib : i ∉ b := by
      rcases hb with hb | hb
      · exact absurd hb hzb
      · exact hb
    have heq : insert z (a.erase i) ∩ b = (a ∩ b).erase i := by
      rw [← Finset.erase_inter i a b]
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxb⟩
        · exact absurd hxb hzb
        · exact ⟨hx, hxb⟩
      · rintro ⟨hx, hxb⟩
        exact ⟨Or.inr hx, hxb⟩
    rw [heq, Finset.erase_eq_of_notMem (fun h => hib (Finset.mem_inter.mp h).2)]

/-- F3: if both sets shift, the two "mixed" intersections both equal `(a ∩ b).erase i`. -/
lemma compress_inter_eq_of_shifts (z i : Fin n) (hzi : z ≠ i) {a b : Finset (Fin n)}
    (ha : Shifts z i a) (hb : Shifts z i b) :
    cpr z i a ∩ b = (a ∩ b).erase i ∧ a ∩ cpr z i b = (a ∩ b).erase i := by
  rw [compress_singleton_eq z i hzi a, compress_singleton_eq z i hzi b, if_pos ha, if_pos hb]
  obtain ⟨haz, hai⟩ := ha
  obtain ⟨hbz, hbi⟩ := hb
  constructor
  · ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨rfl | hx, hxb⟩
      · exact absurd hxb hbz
      · tauto
    · intro hx
      tauto
  · ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hxa, rfl | hx⟩
      · exact absurd hxa haz
      · tauto
    · intro hx
      tauto

/-- F4: if both sets shift, `cpr` preserves the intersection size exactly. -/
lemma card_compress_inter_of_shifts (z i : Fin n) (hzi : z ≠ i) {a b : Finset (Fin n)}
    (ha : Shifts z i a) (hb : Shifts z i b) : (cpr z i a ∩ cpr z i b).card = (a ∩ b).card := by
  rw [compress_singleton_eq z i hzi a, compress_singleton_eq z i hzi b, if_pos ha, if_pos hb]
  obtain ⟨haz, hai⟩ := ha
  obtain ⟨hbz, hbi⟩ := hb
  have heq : insert z (a.erase i) ∩ insert z (b.erase i)
      = insert z ((a.erase i) ∩ (b.erase i)) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hxa, hxb⟩
      rcases hxa with rfl | hxa
      · exact Or.inl rfl
      · rcases hxb with rfl | hxb
        · exact Or.inl rfl
        · exact Or.inr ⟨hxa, hxb⟩
    · rintro (rfl | ⟨hxa, hxb⟩)
      · exact ⟨Or.inl rfl, Or.inl rfl⟩
      · exact ⟨Or.inr hxa, Or.inr hxb⟩
  rw [heq]
  have hznotin : z ∉ (a.erase i) ∩ (b.erase i) := by
    intro hmem
    rw [Finset.mem_inter, Finset.mem_erase, Finset.mem_erase] at hmem
    exact haz hmem.1.2
  rw [Finset.card_insert_of_notMem hznotin]
  have herase : (a.erase i) ∩ (b.erase i) = (a ∩ b).erase i := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase]
    tauto
  rw [herase, Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hai, hbi⟩)]
  have hmem : i ∈ a ∩ b := Finset.mem_inter.mpr ⟨hai, hbi⟩
  have hpos : 0 < (a ∩ b).card := Finset.card_pos.mpr ⟨i, hmem⟩
  omega

/-- **Compression preserves `t`-intersecting.** If `𝒜` is `t`-intersecting then so is
its UV-compression along the singletons `{z}` and `{i}`. -/
theorem TIntersecting.compression (z i : Fin n) (hzi : z ≠ i) {t : ℕ}
    {𝒜 : Finset (Finset (Fin n))} (h𝒜 : TIntersecting t 𝒜) :
    TIntersecting t (𝓒 ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) 𝒜) := by
  -- Key half-lemma: if `A'` is "kept" (both `A'` and its shift are already in `𝒜`),
  -- then `A'` intersects the shift of every `B ∈ 𝒜` in at least `t` elements.
  have key : ∀ A' ∈ 𝒜, cpr z i A' ∈ 𝒜 → ∀ B ∈ 𝒜, t ≤ (A' ∩ cpr z i B).card := by
    intro A' hA'mem hcA' B hBmem
    by_cases hsB : Shifts z i B
    · by_cases hsA' : Shifts z i A'
      · have heq1 := (compress_inter_eq_of_shifts z i hzi hsA' hsB).1
        have heq2 := (compress_inter_eq_of_shifts z i hzi hsA' hsB).2
        have hge : t ≤ (cpr z i A' ∩ B).card := h𝒜 (cpr z i A') hcA' B hBmem
        rw [heq1] at hge
        rw [heq2]
        exact hge
      · have h1 : t ≤ (A' ∩ B).card := h𝒜 A' hA'mem B hBmem
        have h2 : (B ∩ A').card ≤ (cpr z i B ∩ A').card :=
          card_le_card_compress_inter z i hzi hsB hsA'
        rw [Finset.inter_comm B A'] at h2
        rw [Finset.inter_comm A' (cpr z i B)]
        omega
    · have hcBeq : cpr z i B = B := by
        rw [compress_singleton_eq z i hzi]; exact if_neg hsB
      rw [hcBeq]
      exact h𝒜 A' hA'mem B hBmem
  have key' : ∀ B' ∈ 𝒜, cpr z i B' ∈ 𝒜 → ∀ A ∈ 𝒜, t ≤ (cpr z i A ∩ B').card := by
    intro B' hB'mem hcB' A hAmem
    have := key B' hB'mem hcB' A hAmem
    rwa [Finset.inter_comm] at this
  intro A' hA' B' hB'
  rw [UV.mem_compression] at hA' hB'
  rcases hA' with ⟨hA'mem, hcA'⟩ | ⟨hA'notmem, A, hAmem, hcA_eq0⟩
  · rcases hB' with ⟨hB'mem, hcB'⟩ | ⟨hB'notmem, B, hBmem, hcB_eq0⟩
    · -- K,K
      exact h𝒜 A' hA'mem B' hB'mem
    · -- K,M
      have hcB_eq : cpr z i B = B' := hcB_eq0
      rw [← hcB_eq]
      exact key A' hA'mem hcA' B hBmem
  · have hcA_eq : cpr z i A = A' := hcA_eq0
    rcases hB' with ⟨hB'mem, hcB'⟩ | ⟨hB'notmem, B, hBmem, hcB_eq0⟩
    · -- M,K
      rw [← hcA_eq]
      exact key' B' hB'mem hcB' A hAmem
    · -- M,M
      have hcB_eq : cpr z i B = B' := hcB_eq0
      rw [← hcA_eq, ← hcB_eq]
      have hsA : Shifts z i A := by
        by_contra hs
        have hfix : cpr z i A = A := by
          rw [compress_singleton_eq z i hzi]; exact if_neg hs
        have : A' ∈ 𝒜 := by rw [← hcA_eq, hfix]; exact hAmem
        exact hA'notmem this
      have hsB : Shifts z i B := by
        by_contra hs
        have hfix : cpr z i B = B := by
          rw [compress_singleton_eq z i hzi]; exact if_neg hs
        have : B' ∈ 𝒜 := by rw [← hcB_eq, hfix]; exact hBmem
        exact hB'notmem this
      have hcard := card_compress_inter_of_shifts z i hzi hsA hsB
      have h1 : t ≤ (A ∩ B).card := h𝒜 A hAmem B hBmem
      omega

/-- The measure that strictly decreases under a useful compression: the sum, over all
sets in the family, of `2 ^ a` over their elements `a`. -/
noncomputable def familyMeasure (𝒜 : Finset (Finset (Fin n))) : ℕ :=
  ∑ A ∈ 𝒜, ∑ a ∈ A, 2 ^ (a : ℕ)

lemma weight_insert_erase (z i : Fin n) {A : Finset (Fin n)} (hz : z ∉ A) (hi : i ∈ A) :
    (∑ a ∈ insert z (A.erase i), 2 ^ (a : ℕ)) + 2 ^ (i : ℕ)
      = (∑ a ∈ A, 2 ^ (a : ℕ)) + 2 ^ (z : ℕ) := by
  have hzA' : z ∉ A.erase i := fun h => hz (Finset.mem_of_mem_erase h)
  rw [Finset.sum_insert hzA']
  have hsplit : (∑ a ∈ A, 2 ^ (a : ℕ)) = (∑ a ∈ A.erase i, 2 ^ (a : ℕ)) + 2 ^ (i : ℕ) := by
    rw [add_comm]
    exact (Finset.add_sum_erase A (fun a => 2 ^ (a : ℕ)) hi).symm
  omega

/-- A useful (measure-decreasing) compression: `z < i` and the family is not already
stable under it. -/
lemma familyMeasure_compression_lt (z i : Fin n) (hzi : (z : ℕ) < (i : ℕ))
    {𝒜 : Finset (Finset (Fin n))}
    (hne : 𝓒 ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) 𝒜 ≠ 𝒜) :
    familyMeasure (𝓒 ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) 𝒜) < familyMeasure 𝒜 := by
  have hzi' : z ≠ i := fun h => absurd (h ▸ hzi) (lt_irrefl _)
  rw [UV.compression] at hne ⊢
  have huA : {A ∈ 𝒜 | UV.compress ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) A ∈ 𝒜} ∪
      {A ∈ 𝒜 | UV.compress ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) A ∉ 𝒜} = 𝒜 :=
    Finset.filter_union_filter_not_eq _ _
  have hmovers_ne : ({A ∈ 𝒜 |
      UV.compress ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) A ∉ 𝒜} :
      Finset (Finset (Fin n))).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hne
    rw [Finset.filter_image, hempty, Finset.image_empty, Finset.union_empty]
    rwa [hempty, Finset.union_empty] at huA
  unfold familyMeasure
  rw [Finset.sum_union UV.compress_disjoint]
  conv_rhs => rw [← huA]
  rw [Finset.sum_union (Finset.disjoint_filter_filter_not _ _ _),
    Nat.add_lt_add_iff_left, Finset.filter_image,
    Finset.sum_image UV.compress_injOn]
  apply Finset.sum_lt_sum_of_nonempty hmovers_ne
  intro A hA
  rw [Finset.mem_filter] at hA
  have hcne : UV.compress ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) A ≠ A := by
    intro heq
    apply hA.2
    rw [heq]
    exact hA.1
  have hcpr_eq : cpr z i A = UV.compress ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) A := rfl
  rw [← hcpr_eq] at hcne ⊢
  rw [compress_singleton_eq z i hzi' A] at hcne
  have hshifts : Shifts z i A := by
    by_contra hns
    exact hcne (if_neg hns)
  have hcpr_val : cpr z i A = insert z (A.erase i) := by
    rw [compress_singleton_eq z i hzi' A, if_pos hshifts]
  rw [hcpr_val]
  obtain ⟨haz, hai⟩ := hshifts
  have hweq := weight_insert_erase z i haz hai
  have hpow : 2 ^ (z : ℕ) < 2 ^ (i : ℕ) := Nat.pow_lt_pow_right (by norm_num) hzi
  omega

/-- **Convergence to a fully `z`-compressed family.** Repeatedly compressing a
`t`-intersecting family towards a fixed element `z` terminates in a `t`-intersecting
family of the same cardinality that is stable under every further `z`-compression. -/
theorem exists_compressed_TIntersecting (t : ℕ) (z : Fin n) (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : TIntersecting t 𝒜) :
    ∃ ℬ : Finset (Finset (Fin n)), 𝒜.card = ℬ.card ∧ TIntersecting t ℬ ∧
      ∀ i : Fin n, (z : ℕ) < (i : ℕ) →
        IsCompressed ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) ℬ := by
  classical
  by_cases hex : ∃ i : Fin n, (z : ℕ) < (i : ℕ) ∧
      ¬ IsCompressed ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) 𝒜
  · obtain ⟨i, hzi, hnc⟩ := hex
    have hzi' : z ≠ i := fun h => absurd (h ▸ hzi) (lt_irrefl _)
    have hlt : familyMeasure (𝓒 ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) 𝒜)
        < familyMeasure 𝒜 := familyMeasure_compression_lt z i hzi hnc
    have hcard : (𝓒 ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) 𝒜).card = 𝒜.card :=
      UV.card_compression _ _ _
    have hTI : TIntersecting t (𝓒 ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) 𝒜) :=
      TIntersecting.compression z i hzi' h𝒜
    obtain ⟨ℬ, hcardB, hTIB, hstable⟩ :=
      exists_compressed_TIntersecting t z (𝓒 ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) 𝒜) hTI
    exact ⟨ℬ, hcard.symm.trans hcardB, hTIB, hstable⟩
  · refine ⟨𝒜, rfl, h𝒜, fun i hi => ?_⟩
    by_contra hcontra
    exact hex ⟨i, hi, hcontra⟩
termination_by familyMeasure 𝒜

/-- If `ℬ` is stable under `compress z i`, every element of `ℬ` already contains its
own compressed image. -/
lemma mem_of_isCompressed (z i : Fin n) {ℬ : Finset (Finset (Fin n))}
    (hstable : IsCompressed ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) ℬ)
    {A : Finset (Fin n)} (hA : A ∈ ℬ) : cpr z i A ∈ ℬ := by
  have h1 : A ∈ 𝓒 ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) ℬ := by
    rw [hstable]; exact hA
  rw [UV.mem_compression] at h1
  rcases h1 with ⟨_, h2⟩ | ⟨h2, _⟩
  · exact h2
  · exact absurd hA h2

/-- **Split lemma, low part.** Sets containing the favored element `z`, with `z` removed,
form a `(t-1)`-intersecting family: a common element dropped from both sides costs exactly one
unit of intersection. -/
theorem tIntersecting_pred_of_mem {t : ℕ} (z : Fin n) {ℬ : Finset (Finset (Fin n))}
    (h𝒜 : TIntersecting t ℬ) :
    TIntersecting (t - 1) ((ℬ.filter (fun A => z ∈ A)).image (fun A => A.erase z)) := by
  intro A' hA' B' hB'
  simp only [Finset.mem_image, Finset.mem_filter] at hA' hB'
  obtain ⟨A, ⟨hAmem, hAz⟩, rfl⟩ := hA'
  obtain ⟨B, ⟨hBmem, hBz⟩, rfl⟩ := hB'
  have h1 : t ≤ (A ∩ B).card := h𝒜 A hAmem B hBmem
  have h2 : A.erase z ∩ B.erase z = (A ∩ B).erase z := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase]
    tauto
  rw [h2, Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hAz, hBz⟩)]
  omega

/-- **Split lemma, high part.** If `ℬ` is fully compressed towards `z` (stable under
`compress z i` for every `i` with `z < i`), sets *avoiding* `z` form a `(t+1)`-intersecting
family: an intersection of exactly `t` would witness a shifted set with too little overlap. -/
theorem tIntersecting_succ_of_notMem_of_stable {t : ℕ} (ht : 1 ≤ t) (z : Fin n)
    {ℬ : Finset (Finset (Fin n))} (h𝒜 : TIntersecting t ℬ)
    (hzmin : ∀ x : Fin n, x ≠ z → (z : ℕ) < (x : ℕ))
    (hstable : ∀ i : Fin n, (z : ℕ) < (i : ℕ) →
      IsCompressed ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) ℬ) :
    TIntersecting (t + 1) (ℬ.filter (fun A => z ∉ A)) := by
  intro A hA B hB
  rw [Finset.mem_filter] at hA hB
  obtain ⟨hAmem, hAz⟩ := hA
  obtain ⟨hBmem, hBz⟩ := hB
  by_contra hlt
  push_neg at hlt
  have hge : t ≤ (A ∩ B).card := h𝒜 A hAmem B hBmem
  have heq : (A ∩ B).card = t := by omega
  have hne : (A ∩ B).Nonempty := by
    rw [← Finset.card_pos, heq]; omega
  obtain ⟨i, hi⟩ := hne
  rw [Finset.mem_inter] at hi
  obtain ⟨hiA, hiB⟩ := hi
  have hiz : i ≠ z := fun h => hAz (h ▸ hiA)
  have hzlt : (z : ℕ) < (i : ℕ) := hzmin i hiz
  have hzine : z ≠ i := fun h => hiz h.symm
  have hshift : Shifts z i A := ⟨hAz, hiA⟩
  have hA'mem : cpr z i A ∈ ℬ := mem_of_isCompressed z i (hstable i hzlt) hAmem
  have hA'val : cpr z i A = insert z (A.erase i) := by
    rw [compress_singleton_eq z i hzine A, if_pos hshift]
  have hinter : cpr z i A ∩ B = (A ∩ B).erase i := by
    rw [hA'val]
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨rfl | hx, hxb⟩
      · exact absurd hxb hBz
      · tauto
    · intro hx
      tauto
  have h3 : t ≤ (cpr z i A ∩ B).card := h𝒜 (cpr z i A) hA'mem B hBmem
  rw [hinter, Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hiA, hiB⟩), heq] at h3
  omega

theorem TIntersecting.map_equiv {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    {t : ℕ} {𝒜 : Finset (Finset α)} (h : TIntersecting t 𝒜) :
    TIntersecting t (𝒜.image (Finset.map e.toEmbedding)) := by
  intro A' hA' B' hB'
  simp only [Finset.mem_image] at hA' hB'
  obtain ⟨A, hAmem, rfl⟩ := hA'
  obtain ⟨B, hBmem, rfl⟩ := hB'
  rw [← Finset.map_inter, Finset.card_map]
  exact h A hAmem B hBmem

theorem card_image_map_equiv {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (𝒜 : Finset (Finset α)) : (𝒜.image (Finset.map e.toEmbedding)).card = 𝒜.card := by
  apply Finset.card_image_of_injective
  intro A B hAB
  have h2 := congrArg (Finset.map e.symm.toEmbedding) hAB
  simpa using h2

variable {α : Type*} [DecidableEq α] {p : α → Prop} [DecidablePred p]

/-- Restricting two sets that both already satisfy `p` to the subtype commutes with
intersection. -/
lemma subtype_inter_of_forall {A B : Finset α} (hA : ∀ x ∈ A, p x) (hB : ∀ x ∈ B, p x) :
    A.subtype p ∩ B.subtype p = (A ∩ B).subtype p := by
  have hAB : ∀ x ∈ A ∩ B, p x := fun x hx => hA x (Finset.mem_of_mem_inter_left hx)
  apply Finset.map_injective (Function.Embedding.subtype p)
  rw [Finset.map_inter, Finset.subtype_map_of_mem hA, Finset.subtype_map_of_mem hB,
    Finset.subtype_map_of_mem hAB]

/-- Restricting a `t`-intersecting family, all of whose members already satisfy `p`,
to the subtype `{x // p x}` preserves both the `t`-intersecting property and the
cardinality. -/
theorem TIntersecting.subtype_of_forall {t : ℕ} {ℬ : Finset (Finset α)}
    (hp : ∀ A ∈ ℬ, ∀ x ∈ A, p x) (h : TIntersecting t ℬ) :
    TIntersecting t (ℬ.image (Finset.subtype p)) ∧
      (ℬ.image (Finset.subtype p)).card = ℬ.card := by
  constructor
  · intro A' hA' B' hB'
    simp only [Finset.mem_image] at hA' hB'
    obtain ⟨A, hAmem, rfl⟩ := hA'
    obtain ⟨B, hBmem, rfl⟩ := hB'
    rw [subtype_inter_of_forall (hp A hAmem) (hp B hBmem)]
    have hcard : ((A ∩ B).subtype p).card = (A ∩ B).card := by
      conv_rhs => rw [← Finset.subtype_map_of_mem
        (fun x hx => hp A hAmem x (Finset.mem_of_mem_inter_left hx))]
      rw [Finset.card_map]
    rw [hcard]
    exact h A hAmem B hBmem
  · apply Finset.card_image_of_injOn
    intro A hAmem B hBmem hAB
    have h1 := Finset.subtype_map_of_mem (hp A hAmem)
    have h2 := Finset.subtype_map_of_mem (hp B hBmem)
    rw [hAB] at h1
    rw [← h1, h2]

/-- Pascal's identity telescopes the two smaller Katona bounds into the bigger one. -/
theorem katonaBound_pascal {n t : ℕ} (ht1 : 1 ≤ t) (htn : t < n) (h2 : 2 ∣ (n + t)) :
    katonaBound (n - 1) (t - 1) + katonaBound (n - 1) (t + 1) = katonaBound n t := by
  obtain ⟨k, hk⟩ := h2
  have hn1 : 1 ≤ n := by omega
  have e1 : (n + t) / 2 = k := by omega
  have e2 : ((n - 1) + (t - 1)) / 2 = k - 1 := by omega
  have e3 : ((n - 1) + (t + 1)) / 2 = k := by omega
  unfold katonaBound
  rw [e1, e2, e3]
  have hk1 : 1 ≤ k := by omega
  have hkn : k ≤ n - 1 := by omega
  set S := ∑ i ∈ Finset.Icc k (n - 1), (n - 1).choose i with hS_def
  set T := ∑ i ∈ Finset.Icc (k - 1) (n - 2), (n - 1).choose i with hT_def
  -- F1: split `Icc (k-1) (n-1)` at its bottom element `k-1`.
  have hsplit1 : Finset.Icc (k - 1) (n - 1) = insert (k - 1) (Finset.Icc k (n - 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have F1 : ∑ i ∈ Finset.Icc (k - 1) (n - 1), (n - 1).choose i = (n - 1).choose (k - 1) + S := by
    rw [hsplit1, Finset.sum_insert (by simp; omega)]
  -- F2: split `Icc (k-1) (n-1)` at its top element `n-1`.
  have hIcc_split : Finset.Icc (k - 1) (n - 1) = insert (n - 1) (Finset.Icc (k - 1) (n - 2)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have F2 : ∑ i ∈ Finset.Icc (k - 1) (n - 1), (n - 1).choose i = 1 + T := by
    rw [hIcc_split, Finset.sum_insert (by simp; omega), Nat.choose_self]
  -- F3: split `Icc k n` at its top element `n`.
  have hpascal : Finset.Icc k n = insert n (Finset.Icc k (n - 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have F3 : ∑ i ∈ Finset.Icc k n, n.choose i = 1 + ∑ i ∈ Finset.Icc k (n - 1), n.choose i := by
    rw [hpascal, Finset.sum_insert (by simp; omega), Nat.choose_self]
  -- F4: apply Pascal's rule termwise, then reindex the shadow sum onto `T`.
  have hterm : ∀ i ∈ Finset.Icc k (n - 1),
      n.choose i = (n - 1).choose (i - 1) + (n - 1).choose i := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi1 : 1 ≤ i := by omega
    have hp := Nat.choose_succ_succ (n - 1) (i - 1)
    simp only [Nat.succ_eq_add_one] at hp
    rw [Nat.sub_add_cancel hn1, Nat.sub_add_cancel hi1] at hp
    exact hp
  have hreindex : ∑ i ∈ Finset.Icc k (n - 1), (n - 1).choose (i - 1) = T := by
    rw [hT_def]
    apply Finset.sum_nbij' (fun i => i - 1) (fun i => i + 1)
    · intro i hi; rw [Finset.mem_Icc] at hi ⊢; omega
    · intro i hi; rw [Finset.mem_Icc] at hi ⊢; omega
    · intro i hi; rw [Finset.mem_Icc] at hi; omega
    · intro i hi; rw [Finset.mem_Icc] at hi; omega
    · intro i hi; rfl
  have F4 : ∑ i ∈ Finset.Icc k (n - 1), n.choose i = T + S := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hreindex, hS_def]
  rw [F1, F3, F4]
  omega

-- Base case t = n: an n-intersecting family on an n-element ground set has at most
-- one member, which must be the whole set, matching `katonaBound n n = 1`.
lemma katonaBound_self (n : ℕ) : katonaBound n n = 1 := by
  unfold katonaBound
  have : (n + n) / 2 = n := by omega
  rw [this, Finset.Icc_self, Finset.sum_singleton, Nat.choose_self]

theorem katona_base_n {n : ℕ} (𝒜 : Finset (Finset (Fin n))) (h : TIntersecting n 𝒜) :
    𝒜.card ≤ katonaBound n n := by
  rw [katonaBound_self]
  rcases Finset.eq_empty_or_nonempty 𝒜 with rfl | ⟨A, hA⟩
  · simp
  · have hAle : A.card ≤ n := by
      calc A.card ≤ Fintype.card (Fin n) := Finset.card_le_univ A
      _ = n := Fintype.card_fin n
    have hAge : n ≤ A.card := by
      have h1 : n ≤ (A ∩ A).card := h A hA A hA
      rwa [Finset.inter_self] at h1
    have hAcard : A.card = n := le_antisymm hAle hAge
    have hAuniv : A = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hAcard, Fintype.card_fin]
    have hall : ∀ B ∈ 𝒜, B = A := by
      intro B hB
      have h1 : n ≤ (A ∩ B).card := h A hA B hB
      have h2 : (A ∩ B).card ≤ B.card := by
        rw [Finset.inter_comm]
        exact Finset.card_le_card Finset.inter_subset_left
      have h3 : B.card ≤ n := by
        calc B.card ≤ Fintype.card (Fin n) := Finset.card_le_univ B
        _ = n := Fintype.card_fin n
      have hBcard : B.card = n := by omega
      have hBuniv : B = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [hBcard, Fintype.card_fin]
      rw [hAuniv, hBuniv]
    have hsub : 𝒜 ⊆ {A} := by
      intro B hB
      rw [Finset.mem_singleton]
      exact hall B hB
    calc 𝒜.card ≤ ({A} : Finset (Finset (Fin n))).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton A

-- Base case t = 1: a 1-intersecting family is a `Set.Intersecting` family, and
-- `katonaBound n 1 = 2 ^ (n - 1)` when `n` is odd.
lemma katonaBound_one {n : ℕ} (hodd : Odd n) : katonaBound n 1 = 2 ^ (n - 1) := by
  obtain ⟨m, hm⟩ := hodd
  subst hm
  unfold katonaBound
  have hidx : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [hidx]
  have htotal : ∑ i ∈ Finset.range (2 * m + 1 + 1), (2 * m + 1).choose i = 2 ^ (2 * m + 1) :=
    Nat.sum_range_choose (2 * m + 1)
  have hlow : ∑ i ∈ Finset.range (m + 1), (2 * m + 1).choose i = 4 ^ m :=
    Nat.sum_range_choose_halfway m
  have hsplit : Finset.range (2 * m + 1 + 1)
      = Finset.range (m + 1) ∪ Finset.Icc (m + 1) (2 * m + 1) := by
    ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.range (m + 1)) (Finset.Icc (m + 1) (2 * m + 1)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Icc] at hb
    omega
  rw [hsplit, Finset.sum_union hdisj, hlow] at htotal
  have h4m : (4 : ℕ) ^ m = 2 ^ (2 * m) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have h2n : (2 : ℕ) ^ (2 * m + 1) = 2 * 2 ^ (2 * m) := by
    rw [pow_succ]; ring
  have hgoal : 2 * m + 1 - 1 = 2 * m := by omega
  rw [hgoal]
  omega

theorem katona_base_one {n : ℕ} (hodd : Odd n) (𝒜 : Finset (Finset (Fin n)))
    (h : TIntersecting 1 𝒜) : 𝒜.card ≤ katonaBound n 1 := by
  rw [katonaBound_one hodd]
  have hint : (𝒜 : Set (Finset (Fin n))).Intersecting := by
    intro A hA B hB hdisj
    have := h A hA B hB
    rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
    simp [hdisj] at this
  have hle := hint.card_le (α := Finset (Fin n))
  rw [Fintype.card_finset, Fintype.card_fin] at hle
  have h2 : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    have hn1 : 1 ≤ n := by
      obtain ⟨k, hk⟩ := hodd
      omega
    rw [← pow_succ']
    congr 1
    omega
  omega

/-- **Katona's intersection theorem** (even case). For `2 ∣ (n + t)`, a `t`-intersecting
family of subsets of an `n`-element set has size at most `katonaBound n t`. -/
theorem katona (n : ℕ) : ∀ t, 1 ≤ t → t ≤ n → 2 ∣ (n + t) →
    ∀ 𝒜 : Finset (Finset (Fin n)), TIntersecting t 𝒜 → 𝒜.card ≤ katonaBound n t := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t ht1 htn h2 𝒜 h𝒜
    by_cases ht1' : t = 1
    · subst ht1'
      have hodd : Odd n := by
        rw [Nat.odd_iff]
        omega
      exact katona_base_one hodd 𝒜 h𝒜
    by_cases htn' : t = n
    · subst htn'
      exact katona_base_n 𝒜 h𝒜
    have ht2 : 1 < t := by omega
    have hn2 : 2 ≤ n := by omega
    have htn_strict : t < n := by omega
    set z : Fin n := ⟨0, by omega⟩ with hz_def
    obtain ⟨ℬ, hcardB, hTIB, hstable⟩ := exists_compressed_TIntersecting t z 𝒜 h𝒜
    have hz0 : (z : ℕ) = 0 := by rw [hz_def]
    have hzmin : ∀ x : Fin n, x ≠ z → (z : ℕ) < (x : ℕ) := by
      intro x hx
      have hxne : (x : ℕ) ≠ 0 := by
        intro h
        apply hx
        apply Fin.ext
        simp [hz_def, h]
      omega
    have hpred := tIntersecting_pred_of_mem z hTIB
    have hsucc := tIntersecting_succ_of_notMem_of_stable (by omega) z hTIB hzmin hstable
    have hforall_pred : ∀ A ∈ (ℬ.filter (fun A => z ∈ A)).image (fun A => A.erase z),
        ∀ x ∈ A, x ≠ z := by
      intro A hA x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hA
      obtain ⟨A0, -, rfl⟩ := hA
      exact (Finset.mem_erase.mp hx).1
    have hforall_succ : ∀ A ∈ ℬ.filter (fun A => z ∉ A), ∀ x ∈ A, x ≠ z := by
      intro A hA x hx
      rw [Finset.mem_filter] at hA
      exact fun h => hA.2 (h ▸ hx)
    set predSub := (ℬ.filter (fun A => z ∈ A)).image (fun A => A.erase z) with hpredSub_def
    set succSub := ℬ.filter (fun A => z ∉ A) with hsuccSub_def
    obtain ⟨hpred_sub_TI, hpred_sub_card⟩ :=
      TIntersecting.subtype_of_forall (p := fun x : Fin n => x ≠ z) hforall_pred hpred
    obtain ⟨hsucc_sub_TI, hsucc_sub_card⟩ :=
      TIntersecting.subtype_of_forall (p := fun x : Fin n => x ≠ z) hforall_succ hsucc
    have hcard_subtype : Fintype.card {x : Fin n // x ≠ z} = n - 1 := by
      have h1 := Fintype.card_subtype_compl (α := Fin n) (fun x => x = z)
      rw [Fintype.card_subtype_eq, Fintype.card_fin] at h1
      exact h1
    let e : {x : Fin n // x ≠ z} ≃ Fin (n - 1) := Fintype.equivFinOfCardEq hcard_subtype
    set predSubtype := predSub.image (Finset.subtype (fun x : Fin n => x ≠ z)) with hpredSubtype_def
    set succSubtype := succSub.image (Finset.subtype (fun x : Fin n => x ≠ z)) with hsuccSubtype_def
    have hpred_final_TI := hpred_sub_TI.map_equiv e
    have hpred_final_card := card_image_map_equiv e predSubtype
    have hsucc_final_TI := hsucc_sub_TI.map_equiv e
    have hsucc_final_card := card_image_map_equiv e succSubtype
    have hpred_bound := ih (n - 1) (by omega) (t - 1) (by omega) (by omega) (by omega) _ hpred_final_TI
    have hsucc_bound := ih (n - 1) (by omega) (t + 1) (by omega) (by omega) (by omega) _ hsucc_final_TI
    have hpascal := katonaBound_pascal (n := n) (t := t) (by omega) htn_strict h2
    have hcard1 : predSub.card = (ℬ.filter (fun A => z ∈ A)).card := by
      rw [hpredSub_def]
      apply Finset.card_image_of_injOn
      intro A hA B hB hAB
      rw [Finset.mem_coe, Finset.mem_filter] at hA hB
      have hzA : z ∈ A := hA.2
      have hzB : z ∈ B := hB.2
      have := congrArg (insert z) hAB
      rwa [Finset.insert_erase hzA, Finset.insert_erase hzB] at this
    have hsplit : ℬ.card = (ℬ.filter (fun A => z ∈ A)).card + succSub.card := by
      rw [hsuccSub_def, ← Finset.card_filter_add_card_filter_not (fun A => z ∈ A)]
    omega


/-- **Katona's union theorem** (even case), derived from the intersection theorem by
complementation. A family with all pairwise unions of size at most `2d` has size at most
the Hamming ball of radius `d`. -/
theorem katona_union {n d : ℕ} (hd : 2 * d < n) (F : Finset (Finset (Fin n)))
    (hF : ∀ A ∈ F, ∀ B ∈ F, (A ∪ B).card ≤ 2 * d) :
    F.card ≤ ∑ i ∈ Finset.range (d + 1), n.choose i := by
  set t := n - 2 * d with ht_def
  have ht1 : 1 ≤ t := by omega
  have htn : t ≤ n := by omega
  have h2 : 2 ∣ (n + t) := by omega
  have hcompl_TI : TIntersecting t (F.image (compl)) := by
    intro A' hA' B' hB'
    simp only [Finset.mem_image] at hA' hB'
    obtain ⟨A, hAmem, rfl⟩ := hA'
    obtain ⟨B, hBmem, rfl⟩ := hB'
    have hunion := hF A hAmem B hBmem
    have hcompl_eq : Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ := (compl_union A B).symm
    rw [hcompl_eq, Finset.card_compl, Fintype.card_fin]
    omega
  have hcard := katona n t ht1 htn h2 (F.image (compl)) hcompl_TI
  have hcard_eq : (F.image (compl)).card = F.card :=
    Finset.card_image_of_injective F compl_injective
  rw [hcard_eq] at hcard
  have hbound : katonaBound n t = ∑ i ∈ Finset.range (d + 1), n.choose i := by
    unfold katonaBound
    have hidx : (n + t) / 2 = n - d := by omega
    rw [hidx]
    apply Finset.sum_nbij' (fun i => n - i) (fun i => n - i)
    · intro i hi; rw [Finset.mem_Icc] at hi; rw [Finset.mem_range]; omega
    · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Icc]; omega
    · intro i hi; rw [Finset.mem_Icc] at hi; omega
    · intro i hi; rw [Finset.mem_range] at hi; omega
    · intro i hi
      rw [Finset.mem_Icc] at hi
      exact (Nat.choose_symm (by omega)).symm
  rw [hbound] at hcard
  exact hcard

end Katona

open Katona

theorem solution {n d : ℕ} (hd : 2 * d < n) (F : Finset (Finset (Fin n)))
    (hF : ∀ A ∈ F, ∀ B ∈ F, (A ∪ B).card ≤ 2 * d) :
    F.card ≤ ∑ i ∈ Finset.range (d + 1), n.choose i :=
  katona_union hd F hF
