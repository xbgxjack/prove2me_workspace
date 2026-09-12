import Definitions.Def_GYGraphTheory
import Mathlib

namespace GYGraphTheory

variable {n : ℕ} [NeZero n]

noncomputable abbrev activeD (G : SimpleGraph (Fin n)) (L : Finset (Fin n)) :
    SimpleGraph {x // x ∈ L} :=
  G.induce (↑L : Set (Fin n))

noncomputable def activeUnivIsoD (G : SimpleGraph (Fin n)) :
    activeD G (Finset.univ : Finset (Fin n)) ≃g G where
  toFun a := a.1
  invFun v := ⟨v, Finset.mem_univ v⟩
  left_inv a := by ext; rfl
  right_inv v := rfl
  map_rel_iff' := by intro a b; simp only [activeD, SimpleGraph.induce_adj]; rfl

lemma reachable_of_isolated (G : SimpleGraph (Fin n)) {u v : Fin n} (hiso : G.IsIsolated u)
    (h : G.Reachable u v) : u = v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hiso _)

/-- Main invariant: at every stage of decoding, the constructed graph's support lies in the
active label set `L`, the graph is acyclic, and it is connected when restricted to `L`. -/
lemma pruferDecodeAux_invariant (ps : List (Fin n)) :
    ∀ L : Finset (Fin n), L.card = ps.length + 2 → ps.toFinset ⊆ L →
      (pruferDecodeAux ps L).support ⊆ (↑L : Set (Fin n)) ∧
      (pruferDecodeAux ps L).IsAcyclic ∧
      (activeD (pruferDecodeAux ps L) L).Connected := by
  induction ps with
  | nil =>
    intro L hcard hsub
    show (SimpleGraph.fromEdgeSet {s(L.min.getD 0, (L.erase (L.min.getD 0)).min.getD 0)}).support
        ⊆ (↑L : Set (Fin n)) ∧
      (SimpleGraph.fromEdgeSet {s(L.min.getD 0, (L.erase (L.min.getD 0)).min.getD 0)}).IsAcyclic ∧
      ((SimpleGraph.fromEdgeSet {s(L.min.getD 0, (L.erase (L.min.getD 0)).min.getD 0)}).induce
        (↑L : Set (Fin n))).Connected
    have hLne : L.Nonempty := Finset.card_pos.mp (by omega)
    have haL : L.min.getD 0 = L.min' hLne := by
      show L.min.getD 0 = _
      rw [← Finset.coe_min' hLne]; rfl
    have ha_mem : L.min.getD 0 ∈ L := haL ▸ Finset.min'_mem _ _
    set a := L.min.getD 0 with ha_def
    have hLe_ne : (L.erase a).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha_mem]; omega)
    have hbL : (L.erase a).min.getD 0 = (L.erase a).min' hLe_ne := by
      show (L.erase a).min.getD 0 = _
      rw [← Finset.coe_min' hLe_ne]; rfl
    have hb_mem : (L.erase a).min.getD 0 ∈ L.erase a := hbL ▸ Finset.min'_mem _ _
    set b := (L.erase a).min.getD 0 with hb_def
    have hab_ne : a ≠ b := (Finset.mem_erase.mp hb_mem).1.symm
    have hb_memL : b ∈ L := Finset.mem_of_mem_erase hb_mem
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      rw [SimpleGraph.mem_support] at hv
      obtain ⟨w, hvw⟩ := hv
      rw [SimpleGraph.fromEdgeSet_adj] at hvw
      have heq : s(v, w) = s(a, b) := hvw.1
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1]; exact ha_mem
      · rw [h1]; exact hb_memL
    · have hbot : ¬ (⊥ : SimpleGraph (Fin n)).Reachable a b := by
        rw [SimpleGraph.reachable_bot]; exact hab_ne
      have := SimpleGraph.isAcyclic_bot.sup_edge_of_not_reachable hbot
      simpa [SimpleGraph.edge] using this
    · have hcardab : ({a, b} : Finset (Fin n)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hab_ne]), Finset.card_singleton]
      have hLeq : ({a, b} : Finset (Fin n)) = L := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact ha_mem
          · rw [Finset.mem_singleton] at hx; rw [hx]; exact hb_memL
        · rw [hcard, hcardab]; simp
      have hadj : SimpleGraph.fromEdgeSet ({s(a, b)} : Set (Sym2 (Fin n))) |>.Adj a b := by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨rfl, hab_ne⟩
      have hconn := SimpleGraph.induce_pair_connected_of_adj hadj
      have hset : ({a, b} : Set (Fin n)) = (↑L : Set (Fin n)) := by
        rw [← hLeq]; simp
      exact hset ▸ hconn
  | cons p ps ih =>
    intro L hcard hsub
    have hpsub : (p :: ps).toFinset ⊆ L := hsub
    have hcard' : L.card = (p :: ps).length + 2 := hcard
    -- Nonemptiness of the "available label" set
    have hDcard : (L \ (p :: ps).toFinset).card = L.card - (p :: ps).toFinset.card :=
      Finset.card_sdiff_of_subset hpsub
    have hlen : (p :: ps).toFinset.card ≤ (p :: ps).length := (p :: ps).toFinset_card_le
    have hDne : (L \ (p :: ps).toFinset).Nonempty := by
      apply Finset.card_pos.mp
      rw [hDcard]
      simp only [List.length_cons] at hlen hcard'
      omega
    have hkeq : (L \ (p :: ps).toFinset).min.getD 0
        = (L \ (p :: ps).toFinset).min' hDne := by
      show (L \ (p :: ps).toFinset).min.getD 0 = _
      rw [← Finset.coe_min' hDne]; rfl
    have hk_mem : (L \ (p :: ps).toFinset).min.getD 0 ∈ L \ (p :: ps).toFinset :=
      hkeq ▸ Finset.min'_mem _ _
    set k := (L \ (p :: ps).toFinset).min.getD 0 with hk_def
    have hk_memL : k ∈ L := (Finset.mem_sdiff.mp hk_mem).1
    have hk_notmem : k ∉ (p :: ps).toFinset := (Finset.mem_sdiff.mp hk_mem).2
    have hk_ne_p : k ≠ p := fun h => hk_notmem (h ▸ List.mem_toFinset.mpr (List.mem_cons_self))
    have hk_notmem_ps : k ∉ ps.toFinset := by
      intro h
      apply hk_notmem
      rw [List.toFinset_cons]
      exact Finset.mem_insert_of_mem h
    have hp_memL : p ∈ L := by
      apply hsub
      rw [List.toFinset_cons]
      exact Finset.mem_insert_self p ps.toFinset
    have hp_ne_k : p ≠ k := hk_ne_p.symm
    have hp_memLek : p ∈ L.erase k := Finset.mem_erase.mpr ⟨hp_ne_k, hp_memL⟩
    have hcard_erase : (L.erase k).card = ps.length + 2 := by
      rw [Finset.card_erase_of_mem hk_memL]
      simp only [List.length_cons] at hcard'
      omega
    have hsub_erase : ps.toFinset ⊆ L.erase k := by
      rw [Finset.subset_erase]
      refine ⟨?_, hk_notmem_ps⟩
      intro x hx
      apply hsub
      rw [List.toFinset_cons]
      exact Finset.mem_insert_of_mem hx
    obtain ⟨hsupp', hacyc', hconn'⟩ := ih (L.erase k) hcard_erase hsub_erase
    set G' := pruferDecodeAux ps (L.erase k) with hG'_def
    show (G' ⊔ SimpleGraph.fromEdgeSet {s(k, p)}).support ⊆ (↑L : Set (Fin n)) ∧
      (G' ⊔ SimpleGraph.fromEdgeSet {s(k, p)}).IsAcyclic ∧
      (activeD (G' ⊔ SimpleGraph.fromEdgeSet {s(k, p)}) L).Connected
    have hiso_k : G'.IsIsolated k := by
      intro w hadj
      exact (Finset.mem_erase.mp (hsupp' ⟨w, hadj⟩)).1 rfl
    have hnreach : ¬ G'.Reachable k p := fun h =>
      hp_ne_k (reachable_of_isolated G' hiso_k h).symm
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      rw [SimpleGraph.mem_support] at hv
      obtain ⟨w, hvw⟩ := hv
      rw [SimpleGraph.sup_adj] at hvw
      rcases hvw with hvw | hvw
      · exact Finset.mem_of_mem_erase (hsupp' ⟨w, hvw⟩)
      · rw [SimpleGraph.fromEdgeSet_adj] at hvw
        rcases Sym2.eq_iff.mp hvw.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1]; exact hk_memL
        · rw [h1]; exact hp_memL
    · exact hacyc'.sup_edge_of_not_reachable hnreach
    · have hadjGtot : (G' ⊔ SimpleGraph.fromEdgeSet {s(k, p)}).Adj p k := by
        rw [SimpleGraph.sup_adj]
        right
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨Sym2.eq_swap, hp_ne_k⟩
      have hrestrict : (G' ⊔ SimpleGraph.fromEdgeSet {s(k, p)}).induce (↑(L.erase k) : Set (Fin n))
          = G'.induce (↑(L.erase k) : Set (Fin n)) := by
        ext a b
        simp only [SimpleGraph.induce_adj, SimpleGraph.sup_adj]
        constructor
        · rintro (h | h)
          · exact h
          · exfalso
            rw [SimpleGraph.fromEdgeSet_adj] at h
            rcases Sym2.eq_iff.mp h.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact (Finset.mem_erase.mp a.2).1 h1
            · exact (Finset.mem_erase.mp b.2).1 h2
        · exact Or.inl
      have hpre1 : ((G' ⊔ SimpleGraph.fromEdgeSet {s(k, p)}).induce
          (↑(L.erase k) : Set (Fin n))).Preconnected := by
        rw [hrestrict]; exact hconn'.preconnected
      have hpre2 : ((G' ⊔ SimpleGraph.fromEdgeSet {s(k, p)}).induce
          ({k} : Set (Fin n))).Preconnected := by
        rw [SimpleGraph.induce_singleton_eq_top]
        exact fun u v => by
          have : u = v := Subsingleton.elim u v
          rw [this]
      have hconnGtot := SimpleGraph.connected_induce_union hpre1 hpre2
        hp_memLek (Set.mem_singleton k) hadjGtot
      have hset : (↑(L.erase k) : Set (Fin n)) ∪ ({k} : Set (Fin n)) = (↑L : Set (Fin n)) := by
        rw [Set.union_comm, ← Set.insert_eq, ← Finset.coe_insert, Finset.insert_erase hk_memL]
      show (SimpleGraph.induce (↑L : Set (Fin n))
          (G' ⊔ SimpleGraph.fromEdgeSet {s(k, p)})).Connected
      exact hset ▸ hconnGtot

end GYGraphTheory

open GYGraphTheory

theorem solution {n : ℕ} (hn : 2 ≤ n) (s : Fin (n - 2) → Fin n) :
    haveI : NeZero n := ⟨by omega⟩
    (pruferDecode s).IsTree := by
  haveI : NeZero n := ⟨by omega⟩
  have hlen : (List.ofFn s).length = n - 2 := List.length_ofFn
  have hcard : (Finset.univ : Finset (Fin n)).card = (List.ofFn s).length + 2 := by
    rw [hlen, Finset.card_univ, Fintype.card_fin]; omega
  have hsub : (List.ofFn s).toFinset ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
  obtain ⟨hsupp, hacyc, hconn⟩ := pruferDecodeAux_invariant (List.ofFn s) Finset.univ hcard hsub
  show (pruferDecode s).IsTree
  refine ⟨?_, hacyc⟩
  exact (activeUnivIsoD (pruferDecodeAux (List.ofFn s) Finset.univ)).connected_iff.mp hconn
