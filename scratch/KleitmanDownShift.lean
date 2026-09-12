import Mathlib

open Finset Down
open scoped FinsetFamily symmDiff

variable {n : ℕ}

/-- The family `𝒜` has diameter at most `s`: every two members (allowing equality)
have symmetric difference of size at most `s`. -/
def DiamLe (s : ℕ) (𝒜 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∆ B).card ≤ s

lemma erase_eq_symmDiff_singleton {a : Fin n} {x : Finset (Fin n)} (ha : a ∈ x) :
    x.erase a = x ∆ {a} := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_symmDiff, Finset.mem_singleton]
  by_cases hy : y = a <;> simp_all

lemma insert_eq_symmDiff_singleton {a : Fin n} {x : Finset (Fin n)} (ha : a ∉ x) :
    insert a x = x ∆ {a} := by
  ext y
  simp only [Finset.mem_insert, Finset.mem_symmDiff, Finset.mem_singleton]
  by_cases hy : y = a <;> simp_all

lemma symmDiff_cancel_right (x y a : Finset (Fin n)) : (x ∆ a) ∆ (y ∆ a) = x ∆ y := by
  ext z
  simp only [Finset.mem_symmDiff]
  tauto

/-- If `E ∈ 𝒜` and `E.erase a ∈ 𝒜`, and `F ∉ 𝒜` while `insert a F ∈ 𝒜`, then
`|E ∆ F| ≤ s`, given `Δ(𝒜) ≤ s`. This is the key case in showing that down-compression
does not increase the diameter. -/
lemma diam_aux {s : ℕ} {a : Fin n} {𝒜 : Finset (Finset (Fin n))} (h𝒜 : DiamLe s 𝒜)
    {E F : Finset (Fin n)} (hE : E ∈ 𝒜 ∧ E.erase a ∈ 𝒜) (hF : F ∉ 𝒜 ∧ insert a F ∈ 𝒜) :
    (E ∆ F).card ≤ s := by
  obtain ⟨hE1, hE2⟩ := hE
  obtain ⟨hF1, hF2⟩ := hF
  have haF : a ∉ F := by
    intro ha
    have heq : insert a F = F := Finset.insert_eq_self.mpr ha
    rw [heq] at hF2
    exact hF1 hF2
  have hinsF : insert a F = F ∆ {a} := insert_eq_symmDiff_singleton haF
  by_cases haE : a ∈ E
  · have herE : E.erase a = E ∆ {a} := erase_eq_symmDiff_singleton haE
    have hbound := h𝒜 (E.erase a) hE2 (insert a F) hF2
    rw [herE, hinsF, symmDiff_cancel_right] at hbound
    exact hbound
  · have hbound := h𝒜 E hE1 (insert a F) hF2
    rw [hinsF] at hbound
    have haEF : a ∉ E ∆ F := by simp [Finset.mem_symmDiff, haE, haF]
    have hkey : E ∆ (F ∆ ({a} : Finset (Fin n))) = insert a (E ∆ F) := by
      rw [← symmDiff_assoc]
      exact (insert_eq_symmDiff_singleton haEF).symm
    rw [hkey, Finset.card_insert_of_notMem haEF] at hbound
    omega

/-- Down-compressing a family towards `a` does not increase its diameter. -/
theorem diam_compression_le {s : ℕ} {a : Fin n} {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : DiamLe s 𝒜) : DiamLe s (𝓓 a 𝒜) := by
  intro E hE F hF
  rw [Down.mem_compression] at hE hF
  rcases hE with hE | hE
  · rcases hF with hF | hF
    · exact h𝒜 E hE.1 F hF.1
    · exact diam_aux h𝒜 hE hF
  · rcases hF with hF | hF
    · rw [symmDiff_comm]; exact diam_aux h𝒜 hF hE
    · obtain ⟨hE1, hE2⟩ := hE
      obtain ⟨hF1, hF2⟩ := hF
      have haE : a ∉ E := by
        intro ha
        have heq : insert a E = E := Finset.insert_eq_self.mpr ha
        rw [heq] at hE2
        exact hE1 hE2
      have haF : a ∉ F := by
        intro ha
        have heq : insert a F = F := Finset.insert_eq_self.mpr ha
        rw [heq] at hF2
        exact hF1 hF2
      have hbound := h𝒜 (insert a E) hE2 (insert a F) hF2
      rw [insert_eq_symmDiff_singleton haE, insert_eq_symmDiff_singleton haF,
        symmDiff_cancel_right] at hbound
      exact hbound

/-- The measure that strictly decreases under a useful down-compression: the sum of
cardinalities of the sets in the family. -/
noncomputable def familyMeasure (𝒜 : Finset (Finset (Fin n))) : ℕ :=
  ∑ A ∈ 𝒜, A.card

lemma familyMeasure_downcompression_lt (a : Fin n) {𝒜 : Finset (Finset (Fin n))}
    (hne : 𝓓 a 𝒜 ≠ 𝒜) : familyMeasure (𝓓 a 𝒜) < familyMeasure 𝒜 := by
  set K := {s ∈ 𝒜 | s.erase a ∈ 𝒜} with hK_def
  set M := {s ∈ 𝒜 | s.erase a ∉ 𝒜} with hM_def
  have hKM : K ∪ M = 𝒜 := Finset.filter_union_filter_not_eq _ _
  have hKM_disj : Disjoint K M := Finset.disjoint_filter_filter_not _ _ _
  have haM : ∀ s ∈ M, a ∈ s := by
    intro s hs
    rw [hM_def, Finset.mem_filter] at hs
    obtain ⟨hs1, hs2⟩ := hs
    by_contra ha
    rw [Finset.erase_eq_of_notMem ha] at hs2
    exact hs2 hs1
  have hinj : Set.InjOn (fun s => s.erase a) (M : Set (Finset (Fin n))) :=
    (Finset.erase_injOn' a).mono (fun s hs => haM s hs)
  have hMimg_disj : Disjoint K (M.image fun s => s.erase a) := by
    rw [Finset.disjoint_left]
    intro x hxK hxM
    rw [Finset.mem_image] at hxM
    obtain ⟨t, htM, rfl⟩ := hxM
    rw [hK_def, Finset.mem_filter] at hxK
    rw [hM_def, Finset.mem_filter] at htM
    exact htM.2 hxK.1
  have hDcompr : 𝓓 a 𝒜 = K ∪ M.image fun s => s.erase a := by
    ext x
    simp only [Finset.mem_union, Down.mem_compression, hK_def, hM_def, Finset.mem_filter,
      Finset.mem_image]
    constructor
    · rintro (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩)
      · exact Or.inl ⟨hx1, hx2⟩
      · have hax : a ∉ x := fun ha => hx1 (by rwa [Finset.insert_eq_self.mpr ha] at hx2)
        have herase_eq : (insert a x).erase a = x := Finset.erase_insert hax
        exact Or.inr ⟨insert a x, ⟨hx2, by rw [herase_eq]; exact hx1⟩, herase_eq⟩
    · rintro (⟨hx1, hx2⟩ | ⟨t, ⟨ht1, ht2⟩, rfl⟩)
      · exact Or.inl ⟨hx1, hx2⟩
      · have hat : a ∈ t := by
          by_contra ha
          rw [Finset.erase_eq_of_notMem ha] at ht2
          exact ht2 ht1
        exact Or.inr ⟨ht2, by rw [Finset.insert_erase hat]; exact ht1⟩
  have hMnonempty : M.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hne
    rw [hDcompr, hempty, Finset.image_empty, Finset.union_empty]
    rwa [hempty, Finset.union_empty] at hKM
  have hmeasure_compr : familyMeasure (𝓓 a 𝒜) =
      (∑ A ∈ K, A.card) + ∑ s ∈ M, (s.erase a).card := by
    unfold familyMeasure
    rw [hDcompr, Finset.sum_union hMimg_disj, Finset.sum_image hinj]
  rw [hmeasure_compr]
  rw [show familyMeasure 𝒜 = (∑ A ∈ K, A.card) + ∑ A ∈ M, A.card by
    unfold familyMeasure; rw [← hKM, Finset.sum_union hKM_disj]]
  apply Nat.add_lt_add_left
  apply Finset.sum_lt_sum_of_nonempty hMnonempty
  intro s hs
  have has : a ∈ s := haM s hs
  rw [Finset.card_erase_of_mem has]
  have : 0 < s.card := Finset.card_pos.mpr ⟨a, has⟩
  omega

/-- `𝒜` is stable under down-compression towards `a`. -/
def IsDownCompressed (a : Fin n) (𝒜 : Finset (Finset (Fin n))) : Prop := 𝓓 a 𝒜 = 𝒜

/-- A family is a complex (downward closed / hereditary) if it contains every subset
of each of its members. -/
def IsComplex (𝒜 : Finset (Finset (Fin n))) : Prop := ∀ s ∈ 𝒜, ∀ t ⊆ s, t ∈ 𝒜

lemma isDownCompressed_erase_mem {a : Fin n} {𝒜 : Finset (Finset (Fin n))}
    (h : IsDownCompressed a 𝒜) {s : Finset (Fin n)} (hs : s ∈ 𝒜) (ha : a ∈ s) :
    s.erase a ∈ 𝒜 := by
  have hs' : s ∈ 𝓓 a 𝒜 := by rw [h]; exact hs
  rw [Down.mem_compression] at hs'
  rcases hs' with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h2
  · exact absurd hs h1

/-- **Convergence to a full complex.** Repeatedly down-compressing a family of
diameter at most `s` (towards each element in turn) terminates in a family of the
same cardinality, still of diameter at most `s`, that is stable under every further
down-compression. -/
theorem exists_compressed_diam (s : ℕ) (𝒜 : Finset (Finset (Fin n))) (h𝒜 : DiamLe s 𝒜) :
    ∃ 𝒟 : Finset (Finset (Fin n)), 𝒜.card = 𝒟.card ∧ DiamLe s 𝒟 ∧
      ∀ a : Fin n, IsDownCompressed a 𝒟 := by
  classical
  by_cases hex : ∃ a : Fin n, ¬ IsDownCompressed a 𝒜
  · obtain ⟨a, hnc⟩ := hex
    have hlt : familyMeasure (𝓓 a 𝒜) < familyMeasure 𝒜 :=
      familyMeasure_downcompression_lt a hnc
    have hcard : (𝓓 a 𝒜).card = 𝒜.card := Down.card_compression a 𝒜
    have hdiam : DiamLe s (𝓓 a 𝒜) := diam_compression_le h𝒜
    obtain ⟨𝒟, hcardD, hdiamD, hstable⟩ := exists_compressed_diam s (𝓓 a 𝒜) hdiam
    exact ⟨𝒟, hcard.symm.trans hcardD, hdiamD, hstable⟩
  · refine ⟨𝒜, rfl, h𝒜, fun a => ?_⟩
    by_contra hcontra
    exact hex ⟨a, hcontra⟩
termination_by familyMeasure 𝒜

/-- Iterating local down-compression at every element produces a full complex. -/
theorem isComplex_of_forall_downCompressed {𝒜 : Finset (Finset (Fin n))}
    (h : ∀ a : Fin n, IsDownCompressed a 𝒜) : IsComplex 𝒜 := by
  intro s hs t hts
  suffices hgen : ∀ k, ∀ s' ∈ 𝒜, t ⊆ s' → (s' \ t).card = k → t ∈ 𝒜 by
    exact hgen (s \ t).card s hs hts rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s' hs' hts' hcard
    by_cases hst : s' \ t = ∅
    · have hsub : s' ⊆ t := Finset.sdiff_eq_empty_iff_subset.mp hst
      rwa [Finset.Subset.antisymm hsub hts'] at hs'
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hst
      rw [Finset.mem_sdiff] at ha
      obtain ⟨has, hat⟩ := ha
      have herase : s'.erase a ∈ 𝒜 := isDownCompressed_erase_mem (h a) hs' has
      have htsub : t ⊆ s'.erase a := by
        intro x hx
        rw [Finset.mem_erase]
        exact ⟨fun heq => hat (heq ▸ hx), hts' hx⟩
      have hsubset : s'.erase a \ t ⊆ s' \ t := by
        intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨Finset.mem_of_mem_erase hx.1, hx.2⟩
      have hssubset : s'.erase a \ t ⊂ s' \ t := by
        rw [Finset.ssubset_iff_of_subset hsubset]
        exact ⟨a, Finset.mem_sdiff.mpr ⟨has, hat⟩,
          fun hcontra => Finset.notMem_erase a s' (Finset.mem_sdiff.mp hcontra).1⟩
      have hlt : (s'.erase a \ t).card < k := by
        rw [← hcard]; exact Finset.card_lt_card hssubset
      exact ih _ hlt (s'.erase a) herase htsub rfl

/-- In a complex (downward-closed) family, every pairwise union is bounded by the
diameter: this is the extra structural fact that connects Kleitman's diameter theorem
to Katona's union theorem. -/
theorem union_le_of_isComplex_diam {s : ℕ} {𝒟 : Finset (Finset (Fin n))}
    (hcomplex : IsComplex 𝒟) (hdiam : DiamLe s 𝒟) :
    ∀ A ∈ 𝒟, ∀ B ∈ 𝒟, (A ∪ B).card ≤ s := by
  intro A hA B hB
  have hBA_mem : B \ A ∈ 𝒟 := hcomplex B hB (B \ A) Finset.sdiff_subset
  have heq : A ∆ (B \ A) = A ∪ B := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hbound := hdiam A hA (B \ A) hBA_mem
  rwa [heq] at hbound
