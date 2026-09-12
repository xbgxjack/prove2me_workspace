import Definitions.Def_GYGraphTheory
import Mathlib

open scoped Classical

namespace GYGraphTheory

variable {n : ℕ} [NeZero n]

/-! ### Structural facts about `pruferPeel` -/

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

/-! ### The induced subgraph on an active set -/

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

/-! ### Removing the least active leaf keeps the active graph connected -/

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

/-- The graph obtained from `active T S` by deleting the leaf `w` matches `active T (S.erase w)`
directly on `Fin n`. -/
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

/-! ### Base case: the active graph on the full vertex set is the original tree -/

noncomputable def activeUnivIso (T : SimpleGraph (Fin n)) :
    active T (Finset.univ : Finset (Fin n)) ≃g T where
  toFun a := a.1
  invFun v := ⟨v, Finset.mem_univ v⟩
  left_inv a := by ext; rfl
  right_inv v := rfl
  map_rel_iff' := by intro a b; simp only [active, SimpleGraph.induce_adj]; rfl

/-! ### The main peeling invariant -/

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

/-! ### The recorded neighbor of the least active leaf -/

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

/-! ### The count invariant: degree splits into recorded count plus remaining active degree -/

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

/-! ### The Prüfer sequence is exactly the final accumulator -/

lemma ofFn_pruferEncode_eq (T : SimpleGraph (Fin n)) :
    List.ofFn (pruferEncode T) = (pruferPeel T (n - 2)).2 := by
  apply List.ext_getElem (by simp [pruferPeel_acc_length])
  intro i h1 h2
  simp only [List.getElem_ofFn]
  have hi2 : i < n - 2 := by simpa using h1
  show (pruferPeel T (i + 1)).2.getD i 0 = (pruferPeel T (n - 2)).2[i]'h2
  rw [← List.getD_eq_getElem _ _ h2]
  exact (pruferPeel_acc_prefix T (by omega) i (by omega)).symm

/-! ### Stability of the accumulated count once a vertex leaves the active set -/

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

/-! ### Both survivors of the final active set are leaves -/

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

end GYGraphTheory

/-! ### Main theorem: Proposition 3.7.1 -/

open GYGraphTheory

theorem solution {n : ℕ} (hn : 2 ≤ n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) (k : Fin n) :
    haveI : NeZero n := ⟨by omega⟩
    T.degree k = (List.ofFn (pruferEncode T)).count k + 1 := by
  haveI : NeZero n := ⟨by omega⟩
  rw [ofFn_pruferEncode_eq T]
  by_cases hcaseA : k ∈ (pruferPeel T (n - 2)).1
  · have hle : n - 2 ≤ n - 2 := le_refl _
    have hcnt := count_invariant T hT (n - 2) hle k hcaseA
    obtain ⟨hcard, htree⟩ := peel_invariant T hT (n - 2) hle
    have hcard2 : (pruferPeel T (n - 2)).1.card = 2 := by omega
    have hdeg1 := final_active_degree_one T (pruferPeel T (n - 2)).1 htree hcard2 k hcaseA
    rw [hcnt, hdeg1]
  · classical
    have hQ : ∃ i, k ∉ (pruferPeel T i).1 := ⟨n - 2, hcaseA⟩
    have hQi0 : k ∉ (pruferPeel T (Nat.find hQ)).1 := Nat.find_spec hQ
    have hi0_le : Nat.find hQ ≤ n - 2 := Nat.find_le hcaseA
    have hi0_pos : 0 < Nat.find hQ := by
      rcases Nat.eq_zero_or_pos (Nat.find hQ) with h0 | hpos
      · exfalso; apply hQi0; rw [h0]; simp [pruferPeel]
      · exact hpos
    set j := Nat.find hQ - 1 with hj_def
    have hi0_eq : Nat.find hQ = j + 1 := by omega
    have hj_le : j ≤ n - 2 := by omega
    have hj_lt : j < Nat.find hQ := by omega
    have hQj : k ∈ (pruferPeel T j).1 := by
      by_contra hcon
      exact Nat.find_min hQ hj_lt hcon
    obtain ⟨hcard, htree⟩ := peel_invariant T hT j hj_le
    have hcard2 : 2 ≤ (pruferPeel T j).1.card := by omega
    have hleafActive := leastActiveLeaf_isActiveLeaf T (pruferPeel T j).1 htree hcard2
    have hleaf_eq : k = leastActiveLeaf T (pruferPeel T j).1 := by
      by_contra hne
      apply hQi0
      rw [hi0_eq, pruferPeel_succ]
      exact Finset.mem_erase.mpr ⟨hne, hQj⟩
    have hcnt := count_invariant T hT j hj_le k hQj
    have hdeg1 : (activeNeighbors T (pruferPeel T j).1 k).card = 1 := by
      rw [hleaf_eq]; exact hleafActive.2
    rw [hdeg1] at hcnt
    have hnbmem := leastActiveLeafNeighbor_mem T (pruferPeel T j).1 hleafActive.2
    have hnb_ne : leastActiveLeafNeighbor T (pruferPeel T j).1 ≠ k := by
      rw [hleaf_eq]
      intro heq
      rw [activeNeighbors, Finset.mem_filter] at hnbmem
      rw [heq] at hnbmem
      exact T.irrefl hnbmem.2
    have hstep : (pruferPeel T (Nat.find hQ)).2.count k = (pruferPeel T j).2.count k := by
      rw [hi0_eq, pruferPeel_succ, List.count_append, List.count_singleton', if_neg hnb_ne]
      omega
    have hstab : (pruferPeel T (n - 2)).2.count k = (pruferPeel T (Nat.find hQ)).2.count k :=
      pruferPeel_count_stable T hT hn k hi0_le hQi0 (n - 2) hi0_le (le_refl _)
    rw [hstab, hstep]
    exact hcnt
