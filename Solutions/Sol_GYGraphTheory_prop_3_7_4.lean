import Definitions.Def_GYGraphTheory
import Mathlib

open scoped Classical

namespace GYGraphTheory

variable {n : ℕ} [NeZero n]

/-! ### Structural facts about `pruferPeel` (encode side, from Prop 3.7.1) -/

lemma pruferPeel_succ (T : SimpleGraph (Fin n)) (i : ℕ) :
    pruferPeel T (i + 1) =
      ((pruferPeel T i).1.erase (leastActiveLeaf T (pruferPeel T i).1),
        (pruferPeel T i).2 ++ [leastActiveLeafNeighbor T (pruferPeel T i).1]) := by
  simp [pruferPeel]

lemma pruferPeel_acc_length (T : SimpleGraph (Fin n)) (i : ℕ) :
    (pruferPeel T i).2.length = i := by
  induction i with
  | zero => simp [pruferPeel]
  | succ i ih => simp [pruferPeel_succ, ih]

lemma pruferPeel_set_subset (T : SimpleGraph (Fin n)) {i j : ℕ} (hij : i ≤ j) :
    (pruferPeel T j).1 ⊆ (pruferPeel T i).1 := by
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp hij
    subst this; rfl
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · have hij' : i ≤ j := Nat.lt_succ_iff.mp h
      simp only [pruferPeel_succ]
      exact (Finset.erase_subset _ _).trans (ih hij')
    · have : i = j + 1 := le_antisymm hij h
      subst this; rfl

lemma pruferPeel_acc_prefix (T : SimpleGraph (Fin n)) {i j : ℕ} (hij : i ≤ j) (idx : ℕ)
    (hidx : idx < i) :
    (pruferPeel T j).2.getD idx 0 = (pruferPeel T i).2.getD idx 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · have hij' : i ≤ j := Nat.lt_succ_iff.mp h
      simp only [pruferPeel_succ]
      rw [List.getD_append _ _ _ _ (by rw [pruferPeel_acc_length]; omega)]
      exact ih hij'
    · have : i = j + 1 := le_antisymm hij h
      subst this; rfl

/-- The subgraph of `T` induced by the active set `S`, as a graph on the subtype `↑S`. -/
noncomputable abbrev active (T : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    SimpleGraph {x // x ∈ S} :=
  T.induce (↑S : Set (Fin n))

lemma active_degree (T : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) (hv : v ∈ S) :
    (active T S).degree (⟨v, hv⟩ : {x // x ∈ S}) = (activeNeighbors T S v).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij' (fun (a : {x // x ∈ S}) (_ : a ∈ (active T S).neighborFinset ⟨v, hv⟩) =>
      (a : Fin n))
    (fun (b : Fin n) (hb : b ∈ activeNeighbors T S v) =>
      (⟨b, (Finset.mem_filter.mp hb).1⟩ : {x // x ∈ S}))
  case hi =>
    intro a ha
    rw [SimpleGraph.mem_neighborFinset] at ha
    rw [activeNeighbors, Finset.mem_filter]
    exact ⟨a.2, ha⟩
  case hj =>
    intro b hb
    rw [activeNeighbors, Finset.mem_filter] at hb
    rw [SimpleGraph.mem_neighborFinset]
    exact hb.2
  case left_inv => intro a ha; rfl
  case right_inv => intro b hb; rfl

lemma exists_isActiveLeaf (T : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hTree : (active T S).IsTree) (hcard : 2 ≤ S.card) :
    ∃ w, IsActiveLeaf T S w := by
  haveI : Nontrivial {x // x ∈ S} := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe]
    omega
  obtain ⟨w, hw⟩ := hTree.exists_vert_degree_one_of_nontrivial
  refine ⟨(w : Fin n), w.2, ?_⟩
  rw [← active_degree T S (w : Fin n) w.2]
  exact hw

lemma leastActiveLeaf_isActiveLeaf (T : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hTree : (active T S).IsTree) (hcard : 2 ≤ S.card) :
    IsActiveLeaf T S (leastActiveLeaf T S) := by
  have hne : (S.filter (IsActiveLeaf T S)).Nonempty := by
    obtain ⟨w, hw⟩ := exists_isActiveLeaf T S hTree hcard
    exact ⟨w, Finset.mem_filter.mpr ⟨hw.1, hw⟩⟩
  have heq : leastActiveLeaf T S = (S.filter (IsActiveLeaf T S)).min' hne := by
    show (S.filter (IsActiveLeaf T S)).min.getD 0 = _
    rw [← Finset.coe_min' hne]
    rfl
  have hmem := Finset.min'_mem (S.filter (IsActiveLeaf T S)) hne
  rw [← heq] at hmem
  exact (Finset.mem_filter.mp hmem).2

noncomputable def eraseIso (T : SimpleGraph (Fin n)) (S : Finset (Fin n)) (w : Fin n)
    (hw : w ∈ S) :
    (active T S).induce ({(⟨w, hw⟩ : {x // x ∈ S})}ᶜ) ≃g active T (S.erase w) where
  toFun a := ⟨(a.1 : Fin n),
    Finset.mem_erase.mpr ⟨fun h => a.2 (Subtype.ext h), a.1.2⟩⟩
  invFun x := ⟨⟨(x : Fin n), (Finset.mem_erase.mp x.2).2⟩,
    fun h => (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h)⟩
  left_inv a := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
  map_rel_iff' := by
    intro a b
    simp only [active, SimpleGraph.induce_adj]
    rfl

lemma active_erase_connected (T : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hTree : (active T S).IsTree) (hcard : 2 ≤ S.card) :
    (active T (S.erase (leastActiveLeaf T S))).Connected := by
  set w := leastActiveLeaf T S with hw_def
  have hleaf := leastActiveLeaf_isActiveLeaf T S hTree hcard
  have hdeg : (active T S).degree (⟨w, hleaf.1⟩ : {x // x ∈ S}) = 1 := by
    rw [active_degree T S w hleaf.1]
    exact hleaf.2
  have hconn := hTree.connected.induce_compl_singleton_of_degree_eq_one hdeg
  exact (eraseIso T S w hleaf.1).connected_iff.mp hconn

noncomputable def activeUnivIso (T : SimpleGraph (Fin n)) :
    active T (Finset.univ : Finset (Fin n)) ≃g T where
  toFun a := a.1
  invFun v := ⟨v, Finset.mem_univ v⟩
  left_inv a := by ext; rfl
  right_inv v := rfl
  map_rel_iff' := by intro a b; simp only [active, SimpleGraph.induce_adj]; rfl

lemma peel_invariant (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    ∀ i, i ≤ n - 2 →
      (pruferPeel T i).1.card = n - i ∧ (active T (pruferPeel T i).1).IsTree := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨by simp [pruferPeel], ?_⟩
    show (active T Finset.univ).IsTree
    exact (activeUnivIso T).isTree_iff.mpr hT
  | succ i ih =>
    intro hi1
    have hi : i ≤ n - 2 := by omega
    obtain ⟨hcard, htree⟩ := ih hi
    have hcard2 : 2 ≤ (pruferPeel T i).1.card := by omega
    have hconn := active_erase_connected T (pruferPeel T i).1 htree hcard2
    have hacyc : (active T ((pruferPeel T i).1.erase
        (leastActiveLeaf T (pruferPeel T i).1))).IsAcyclic :=
      hT.isAcyclic.induce _
    refine ⟨?_, ?_⟩
    · rw [pruferPeel_succ]
      show ((pruferPeel T i).1.erase (leastActiveLeaf T (pruferPeel T i).1)).card = n - (i + 1)
      rw [Finset.card_erase_of_mem
        (leastActiveLeaf_isActiveLeaf T (pruferPeel T i).1 htree hcard2).1]
      omega
    · rw [pruferPeel_succ]
      exact ⟨hconn, hacyc⟩

lemma leastActiveLeafNeighbor_mem (T : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (h : (activeNeighbors T S (leastActiveLeaf T S)).card = 1) :
    leastActiveLeafNeighbor T S ∈ activeNeighbors T S (leastActiveLeaf T S) := by
  have hne : (activeNeighbors T S (leastActiveLeaf T S)).Nonempty := Finset.card_pos.mp (by omega)
  have heq : leastActiveLeafNeighbor T S
      = (activeNeighbors T S (leastActiveLeaf T S)).min' hne := by
    show (activeNeighbors T S (leastActiveLeaf T S)).min.getD 0 = _
    rw [← Finset.coe_min' hne]
    rfl
  rw [heq]
  exact Finset.min'_mem _ _

lemma count_invariant (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    ∀ i, i ≤ n - 2 → ∀ k, k ∈ (pruferPeel T i).1 →
      T.degree k = (pruferPeel T i).2.count k + (activeNeighbors T (pruferPeel T i).1 k).card := by
  intro i
  induction i with
  | zero =>
    intro _ k _
    have h1 : (pruferPeel T 0).2 = [] := by simp [pruferPeel]
    have h2 : (pruferPeel T 0).1 = Finset.univ := by simp [pruferPeel]
    rw [h1, h2]
    have heq : activeNeighbors T Finset.univ k = T.neighborFinset k := by
      ext w
      simp [activeNeighbors, SimpleGraph.mem_neighborFinset]
    simp [heq, SimpleGraph.card_neighborFinset_eq_degree]
  | succ i ih =>
    intro hi1 k hk
    have hi : i ≤ n - 2 := by omega
    obtain ⟨hcard, htree⟩ := peel_invariant T hT i hi
    set S := (pruferPeel T i).1 with hS_def
    set leaf := leastActiveLeaf T S with hleaf_def
    set nb := leastActiveLeafNeighbor T S with hnb_def
    have hcard2 : 2 ≤ S.card := by omega
    have hleafActive : IsActiveLeaf T S leaf := leastActiveLeaf_isActiveLeaf T S htree hcard2
    have hleafcard : (activeNeighbors T S leaf).card = 1 := hleafActive.2
    rw [pruferPeel_succ] at hk
    have hkS : k ∈ S := Finset.mem_of_mem_erase hk
    have IH := ih hi k hkS
    have hnbmem : nb ∈ activeNeighbors T S leaf := leastActiveLeafNeighbor_mem T S hleafActive.2
    have huniq : ∀ x ∈ activeNeighbors T S leaf, ∀ y ∈ activeNeighbors T S leaf, x = y :=
      Finset.card_le_one.mp (by omega)
    have hequiv : nb = k ↔ leaf ∈ activeNeighbors T S k := by
      constructor
      · intro h
        rw [activeNeighbors, Finset.mem_filter]
        refine ⟨hleafActive.1, ?_⟩
        have : k ∈ activeNeighbors T S leaf := h ▸ hnbmem
        rw [activeNeighbors, Finset.mem_filter] at this
        exact this.2.symm
      · intro h
        rw [activeNeighbors, Finset.mem_filter] at h
        apply huniq nb hnbmem k
        rw [activeNeighbors, Finset.mem_filter]
        exact ⟨hkS, h.2.symm⟩
    rw [pruferPeel_succ]
    show T.degree k = ((pruferPeel T i).2 ++ [nb]).count k
      + (activeNeighbors T (S.erase leaf) k).card
    rw [IH, List.count_append]
    have hcardeq : activeNeighbors T (S.erase leaf) k = (activeNeighbors T S k).erase leaf := by
      rw [activeNeighbors, activeNeighbors, Finset.filter_erase]
    rw [hcardeq, Finset.card_erase_eq_ite]
    simp only [List.count_singleton, beq_iff_eq]
    by_cases hc : nb = k
    · have hleafmem : leaf ∈ activeNeighbors T S k := hequiv.mp hc
      have hpos : 0 < (activeNeighbors T S k).card := Finset.card_pos.mpr ⟨leaf, hleafmem⟩
      rw [if_pos hc, if_pos hleafmem]
      omega
    · have hleafnmem : leaf ∉ activeNeighbors T S k := fun h => hc (hequiv.mpr h)
      rw [if_neg hc, if_neg hleafnmem]
      omega

lemma ofFn_pruferEncode_eq (T : SimpleGraph (Fin n)) :
    List.ofFn (pruferEncode T) = (pruferPeel T (n - 2)).2 := by
  apply List.ext_getElem (by simp [pruferPeel_acc_length])
  intro i h1 h2
  simp only [List.getElem_ofFn]
  have hi2 : i < n - 2 := by simpa using h1
  show (pruferPeel T (i + 1)).2.getD i 0 = (pruferPeel T (n - 2)).2[i]'h2
  rw [← List.getD_eq_getElem _ _ h2]
  exact (pruferPeel_acc_prefix T (by omega) i (by omega)).symm

lemma pruferPeel_count_stable (T : SimpleGraph (Fin n)) (hT : T.IsTree) (hn : 2 ≤ n) (k : Fin n)
    {j : ℕ} (hj : j ≤ n - 2) (hk : k ∉ (pruferPeel T j).1) :
    ∀ m, j ≤ m → m ≤ n - 2 → (pruferPeel T m).2.count k = (pruferPeel T j).2.count k := by
  intro m
  induction m with
  | zero =>
    intro hm _
    have : j = 0 := Nat.le_zero.mp hm
    subst this; rfl
  | succ m ih =>
    intro hjm1 hm1
    rcases Nat.lt_or_ge j (m + 1) with h | h
    · have hjm : j ≤ m := Nat.lt_succ_iff.mp h
      have hm : m ≤ n - 2 := by omega
      have hkm : k ∉ (pruferPeel T m).1 := fun hmem => hk (pruferPeel_set_subset T hjm hmem)
      obtain ⟨hcard, htree⟩ := peel_invariant T hT m hm
      have hcard2 : 2 ≤ (pruferPeel T m).1.card := by omega
      have hleafActive := leastActiveLeaf_isActiveLeaf T (pruferPeel T m).1 htree hcard2
      have hnbmem := leastActiveLeafNeighbor_mem T (pruferPeel T m).1 hleafActive.2
      have hnbS : leastActiveLeafNeighbor T (pruferPeel T m).1 ∈ (pruferPeel T m).1 := by
        rw [activeNeighbors, Finset.mem_filter] at hnbmem
        exact hnbmem.1
      have hne : leastActiveLeafNeighbor T (pruferPeel T m).1 ≠ k := fun heq => hkm (heq ▸ hnbS)
      rw [pruferPeel_succ, List.count_append, List.count_singleton', if_neg hne]
      simpa using ih hjm hm
    · have : j = m + 1 := le_antisymm hjm1 h
      subst this; rfl

lemma final_active_degree_one (T : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (htree : (active T S).IsTree) (hcard2 : S.card = 2) (k : Fin n) (hk : k ∈ S) :
    (activeNeighbors T S k).card = 1 := by
  have hall : ∀ w : {x // x ∈ S}, (active T S).degree w = 1 := by
    haveI : Nontrivial {x // x ∈ S} := by
      rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe]
      omega
    obtain ⟨u, v, huv, hu, hv⟩ := htree.exists_ne_and_degree_eq_one
    intro w
    by_contra hw
    have hwu : w ≠ u := fun h => hw (h ▸ hu)
    have hwv : w ≠ v := fun h => hw (h ▸ hv)
    have h3 : ({w, u, v} : Finset {x // x ∈ S}).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hwu, hwv]),
        Finset.card_insert_of_notMem (by simp [huv]), Finset.card_singleton]
    have hle : ({w, u, v} : Finset {x // x ∈ S}).card ≤ Fintype.card {x // x ∈ S} :=
      Finset.card_le_univ _
    rw [Fintype.card_coe] at hle
    omega
  rw [← active_degree T S k hk]
  exact hall ⟨k, hk⟩

/-! ### Structural facts about `pruferDecodeAux` (decode side, from Prop 3.7.3) -/

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

/-! ### The decode-side local count invariant -/

lemma decode_count_invariant (l : List (Fin n)) :
    ∀ L : Finset (Fin n), L.card = l.length + 2 → l.toFinset ⊆ L → ∀ x ∈ L,
      (activeNeighbors (pruferDecodeAux l L) L x).card = l.count x + 1 := by
  induction l with
  | nil =>
    intro L hcard hsub x hx
    show (activeNeighbors
      (SimpleGraph.fromEdgeSet {s(L.min.getD 0, (L.erase (L.min.getD 0)).min.getD 0)}) L x).card
      = 0 + 1
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
    have hcardab : ({a, b} : Finset (Fin n)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hab_ne]), Finset.card_singleton]
    have hLeq : ({a, b} : Finset (Fin n)) = L := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact ha_mem
        · rw [Finset.mem_singleton] at hy; rw [hy]; exact hb_memL
      · rw [hcard, hcardab]; simp
    have hxab : x = a ∨ x = b := by
      rw [← hLeq] at hx
      simpa using hx
    rw [show (0:ℕ) + 1 = 1 from rfl]
    rcases hxab with rfl | rfl
    · have : activeNeighbors (SimpleGraph.fromEdgeSet {s(a, b)}) L a = {b} := by
        ext y
        simp only [activeNeighbors, Finset.mem_filter, Finset.mem_singleton,
          SimpleGraph.fromEdgeSet_adj]
        constructor
        · rintro ⟨hyL, heq, hne⟩
          rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h2
          · exact absurd h1 hab_ne
        · rintro rfl
          exact ⟨hb_memL, rfl, hab_ne⟩
      rw [this, Finset.card_singleton]
    · have : activeNeighbors (SimpleGraph.fromEdgeSet {s(a, b)}) L b = {a} := by
        ext y
        simp only [activeNeighbors, Finset.mem_filter, Finset.mem_singleton,
          SimpleGraph.fromEdgeSet_adj]
        constructor
        · rintro ⟨hyL, heq, hne⟩
          rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact absurd h1 hab_ne.symm
          · exact h2
        · rintro rfl
          exact ⟨ha_mem, Sym2.eq_swap, hab_ne.symm⟩
      rw [this, Finset.card_singleton]
  | cons p ps ih =>
    intro L hcard hsub x hx
    have hpsub : (p :: ps).toFinset ⊆ L := hsub
    have hcard' : L.card = (p :: ps).length + 2 := hcard
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
      intro h; apply hk_notmem; rw [List.toFinset_cons]; exact Finset.mem_insert_of_mem h
    have hp_memL : p ∈ L := by
      apply hsub; rw [List.toFinset_cons]; exact Finset.mem_insert_self p ps.toFinset
    have hp_ne_k : p ≠ k := hk_ne_p.symm
    have hcard_erase : (L.erase k).card = ps.length + 2 := by
      rw [Finset.card_erase_of_mem hk_memL]
      simp only [List.length_cons] at hcard'
      omega
    have hsub_erase : ps.toFinset ⊆ L.erase k := by
      rw [Finset.subset_erase]
      refine ⟨?_, hk_notmem_ps⟩
      intro y hy; apply hsub; rw [List.toFinset_cons]; exact Finset.mem_insert_of_mem hy
    set G' := pruferDecodeAux ps (L.erase k) with hG'_def
    have hsupp' : G'.support ⊆ (↑(L.erase k) : Set (Fin n)) :=
      (pruferDecodeAux_invariant ps (L.erase k) hcard_erase hsub_erase).1
    show (activeNeighbors (G' ⊔ SimpleGraph.fromEdgeSet {s(k, p)}) L x).card = (p :: ps).count x + 1
    have hiso_k : G'.IsIsolated k := by
      intro w hadj
      exact (Finset.mem_erase.mp (hsupp' ⟨w, hadj⟩)).1 rfl
    by_cases hxk : x = k
    · rw [hxk]
      have heqset : activeNeighbors (G' ⊔ SimpleGraph.fromEdgeSet {s(k, p)}) L k = {p} := by
        ext y
        simp only [activeNeighbors, Finset.mem_filter, Finset.mem_singleton,
          SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj]
        constructor
        · rintro ⟨hyL, hG' | ⟨heq, hne⟩⟩
          · exact absurd hG' (hiso_k y)
          · rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact h2
            · exact absurd h1 hk_ne_p
        · rintro rfl
          exact ⟨hp_memL, Or.inr ⟨rfl, hk_ne_p⟩⟩
      rw [heqset, Finset.card_singleton]
      have : (p :: ps).count k = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        exact hk_notmem (List.mem_toFinset.mpr hmem)
      rw [this]
    · by_cases hxp : x = p
      · rw [hxp]
        have hpek : p ∈ L.erase k := Finset.mem_erase.mpr ⟨hp_ne_k, hp_memL⟩
        have IH := ih (L.erase k) hcard_erase hsub_erase p hpek
        have heqset : activeNeighbors (G' ⊔ SimpleGraph.fromEdgeSet {s(k, p)}) L p
            = insert k (activeNeighbors G' (L.erase k) p) := by
          ext y
          simp only [activeNeighbors, Finset.mem_filter, Finset.mem_insert,
            SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj]
          constructor
          · rintro ⟨hyL, hG' | ⟨heq, hne⟩⟩
            · exact Or.inr ⟨Finset.mem_erase.mpr
                ⟨fun h => (hiso_k p (h ▸ hG'.symm)), hyL⟩, hG'⟩
            · rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact absurd h1 hp_ne_k
              · exact Or.inl h2
          · rintro (rfl | ⟨hyLek, hG'⟩)
            · exact ⟨hk_memL, Or.inr ⟨Sym2.eq_swap, hp_ne_k⟩⟩
            · exact ⟨Finset.mem_of_mem_erase hyLek, Or.inl hG'⟩
        rw [heqset]
        rw [Finset.card_insert_of_notMem (by
          intro hmem
          rw [activeNeighbors, Finset.mem_filter] at hmem
          exact Finset.notMem_erase k L hmem.1)]
        rw [IH]
        simp [List.count_cons]
      · have hxLek : x ∈ L.erase k := Finset.mem_erase.mpr ⟨hxk, hx⟩
        have IH := ih (L.erase k) hcard_erase hsub_erase x hxLek
        have heqset : activeNeighbors (G' ⊔ SimpleGraph.fromEdgeSet {s(k, p)}) L x
            = activeNeighbors G' (L.erase k) x := by
          ext y
          simp only [activeNeighbors, Finset.mem_filter, SimpleGraph.sup_adj,
            SimpleGraph.fromEdgeSet_adj]
          constructor
          · rintro ⟨hyL, hG' | ⟨heq, hne⟩⟩
            · exact ⟨Finset.mem_erase.mpr
                ⟨fun h => hiso_k x (h ▸ hG'.symm), hyL⟩, hG'⟩
            · rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact absurd h1 hxk
              · exact absurd h1 hxp
          · rintro ⟨hyLek, hG'⟩
            exact ⟨Finset.mem_of_mem_erase hyLek, Or.inl hG'⟩
        rw [heqset, IH]
        simp only [List.count_cons, beq_iff_eq, if_neg (Ne.symm hxp)]

end GYGraphTheory
