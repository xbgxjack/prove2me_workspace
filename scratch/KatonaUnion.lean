import Mathlib

open Finset UV
open scoped FinsetFamily

def TIntersecting {α : Type*} [DecidableEq α] (t : ℕ) (𝒜 : Finset (Finset α)) : Prop :=
  ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, t ≤ (A ∩ B).card

noncomputable def katonaBound (n t : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc ((n + t) / 2) n, n.choose i

-- Stand-in for the already-proven Katona intersection theorem.
axiom katona (n : ℕ) : ∀ t, 1 ≤ t → t ≤ n → 2 ∣ (n + t) →
    ∀ 𝒜 : Finset (Finset (Fin n)), TIntersecting t 𝒜 → 𝒜.card ≤ katonaBound n t

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
