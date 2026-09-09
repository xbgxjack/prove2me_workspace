import Mathlib

open Finset

def TIntersecting {α : Type*} [DecidableEq α] (t : ℕ) (𝒜 : Finset (Finset α)) : Prop :=
  ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, t ≤ (A ∩ B).card

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
  apply Finset.map_injective (Embedding.subtype p)
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
    have hcard : (A ∩ B).subtype p |>.card = (A ∩ B).card := by
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
