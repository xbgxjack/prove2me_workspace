import Mathlib

open Finset UV
open scoped FinsetFamily

variable {n : ℕ}

def TIntersecting (t : ℕ) (𝒜 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, t ≤ (A ∩ B).card

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
