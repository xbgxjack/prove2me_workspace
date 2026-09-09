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
