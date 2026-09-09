import Mathlib

def TIntersecting {α : Type*} [DecidableEq α] (t : ℕ) (𝒜 : Finset (Finset α)) : Prop :=
  ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, t ≤ (A ∩ B).card

/-- `TIntersecting` transports along a bijection: relabeling the ground set via an
equiv preserves both the intersecting property and the family's cardinality. -/
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
