import Mathlib

open Finset

def TIntersecting {n : ℕ} (t : ℕ) (𝒜 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, t ≤ (A ∩ B).card

-- Base case t = n: an n-intersecting family on an n-element ground set has at most
-- one member, which must be the whole set.
example {n : ℕ} (𝒜 : Finset (Finset (Fin n))) (h : TIntersecting n 𝒜) :
    𝒜.card ≤ 1 := by
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
