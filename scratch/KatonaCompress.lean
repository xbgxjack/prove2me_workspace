import Mathlib

open Finset UV
open scoped FinsetFamily

variable {n : ℕ}

/-- A family of subsets of `Fin n` is `t`-intersecting if every pair of members
(including a set intersected with itself) has intersection size at least `t`. -/
def TIntersecting (t : ℕ) (𝒜 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, t ≤ (A ∩ B).card

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
