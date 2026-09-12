import Mathlib

open Finset UV
open scoped FinsetFamily

def TIntersecting {α : Type*} [DecidableEq α] (t : ℕ) (𝒜 : Finset (Finset α)) : Prop :=
  ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, t ≤ (A ∩ B).card

noncomputable def katonaBound (n t : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc ((n + t) / 2) n, n.choose i

-- Stand-ins for the already-proven pieces (types only, to test the wiring in isolation).
axiom exists_compressed_TIntersecting {n : ℕ} (t : ℕ) (z : Fin n) (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : TIntersecting t 𝒜) :
    ∃ ℬ : Finset (Finset (Fin n)), 𝒜.card = ℬ.card ∧ TIntersecting t ℬ ∧
      ∀ i : Fin n, (z : ℕ) < (i : ℕ) →
        IsCompressed ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) ℬ

axiom tIntersecting_pred_of_mem {n : ℕ} {t : ℕ} (z : Fin n) {ℬ : Finset (Finset (Fin n))}
    (h𝒜 : TIntersecting t ℬ) :
    TIntersecting (t - 1) ((ℬ.filter (fun A => z ∈ A)).image (fun A => A.erase z))

axiom tIntersecting_succ_of_notMem_of_stable {n : ℕ} {t : ℕ} (ht : 1 ≤ t) (z : Fin n)
    {ℬ : Finset (Finset (Fin n))} (h𝒜 : TIntersecting t ℬ)
    (hzmin : ∀ x : Fin n, x ≠ z → (z : ℕ) < (x : ℕ))
    (hstable : ∀ i : Fin n, (z : ℕ) < (i : ℕ) →
      IsCompressed ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) ℬ) :
    TIntersecting (t + 1) (ℬ.filter (fun A => z ∉ A))

axiom TIntersecting.subtype_of_forall {α : Type*} [DecidableEq α] {p : α → Prop}
    [DecidablePred p] {t : ℕ} {ℬ : Finset (Finset α)}
    (hp : ∀ A ∈ ℬ, ∀ x ∈ A, p x) (h : TIntersecting t ℬ) :
    TIntersecting t (ℬ.image (Finset.subtype p)) ∧
      (ℬ.image (Finset.subtype p)).card = ℬ.card

axiom TIntersecting.map_equiv {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    {t : ℕ} {𝒜 : Finset (Finset α)} (h : TIntersecting t 𝒜) :
    TIntersecting t (𝒜.image (Finset.map e.toEmbedding))

axiom card_image_map_equiv {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (𝒜 : Finset (Finset α)) : (𝒜.image (Finset.map e.toEmbedding)).card = 𝒜.card

axiom katonaBound_pascal {n t : ℕ} (ht1 : 1 ≤ t) (htn : t < n) (h2 : 2 ∣ (n + t)) :
    katonaBound (n - 1) (t - 1) + katonaBound (n - 1) (t + 1) = katonaBound n t

/-- The inductive step: given the bound for every smaller ambient size, derive it for `n`
in the case `1 < t < n`. -/
theorem katona_inductive_step {n : ℕ} (hn2 : 2 ≤ n) {t : ℕ} (ht2 : 1 < t) (htn : t < n)
    (h2 : 2 ∣ (n + t))
    (ih : ∀ m, m < n → ∀ t', 1 ≤ t' → t' ≤ m → 2 ∣ (m + t') →
      ∀ 𝒞 : Finset (Finset (Fin m)), TIntersecting t' 𝒞 → 𝒞.card ≤ katonaBound m t')
    (𝒜 : Finset (Finset (Fin n))) (h𝒜 : TIntersecting t 𝒜) :
    𝒜.card ≤ katonaBound n t := by
  set z : Fin n := ⟨0, by omega⟩ with hz_def
  obtain ⟨ℬ, hcardB, hTIB, hstable⟩ := exists_compressed_TIntersecting t z 𝒜 h𝒜
  have hz0 : (z : ℕ) = 0 := by rw [hz_def]
  have hzmin : ∀ x : Fin n, x ≠ z → (z : ℕ) < (x : ℕ) := by
    intro x hx
    have : (x : ℕ) ≠ 0 := by
      intro h
      apply hx
      apply Fin.ext
      simp [hz_def, h]
    omega
  -- Split ℬ into the sets containing `z` (erased, giving a `(t-1)`-intersecting family)
  -- and the sets avoiding `z` (giving a `(t+1)`-intersecting family via full compression).
  have hpred := tIntersecting_pred_of_mem z hTIB
  have hsucc := tIntersecting_succ_of_notMem_of_stable (by omega) z hTIB hzmin hstable
  -- Both live entirely inside `{x : Fin n // x ≠ z}`; restrict to that subtype.
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
  -- Transport `{x : Fin n // x ≠ z}` (card `n - 1`) onto `Fin (n - 1)`.
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
  -- Apply the induction hypothesis at `n - 1 < n`.
  have hpred_bound := ih (n - 1) (by omega) (t - 1) (by omega) (by omega) (by omega) _ hpred_final_TI
  have hsucc_bound := ih (n - 1) (by omega) (t + 1) (by omega) (by omega) (by omega) _ hsucc_final_TI
  have hpascal := katonaBound_pascal (n := n) (t := t) (by omega) htn h2
  -- Assemble: |𝒜| = |ℬ| = |ℬ₁'| + |ℬ₀| ≤ M(n-1,t-1) + M(n-1,t+1) = M(n,t).
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
