import Mathlib
import Definitions.Def_BertsekasGraphSearch

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasGraphSearch V) (H : BertsekasBaseHeuristic G)
    (l : List V) (hrun : BertsekasIsRolloutRun G H l)
    (i₁ : V) (hhead : l.head? = some i₁) (hstart : i₁ ∉ G.dest)
    (d : V) (hlast : l.getLast? = some d) :
    G.cost d = BertsekasHeurCost G H i₁ +
      (l.dropLast.map (BertsekasRolloutDelta G H)).sum := by
  obtain ⟨_hne, hchain, hnodest, dd, hddest, hddlast⟩ := hrun
  have hdd : d = dd := by
    have heq : (some d : Option V) = some dd := hlast.symm.trans hddlast
    exact Option.some_inj.mp heq
  subst hdd
  have hdest' : d ∈ G.dest := hddest
  have hproj : BertsekasProjection G H d = d := by
    unfold BertsekasProjection
    rw [H.hdest d hdest']
    rfl
  have hHeurEq : BertsekasHeurCost G H d = G.cost d := by
    unfold BertsekasHeurCost
    rw [hproj]
  rw [← hHeurEq]
  have key : ∀ (m : List V), List.IsChain (fun a b => b ∈ BertsekasNbrs G a ∧
        ∀ j ∈ BertsekasNbrs G a, BertsekasHeurCost G H b ≤ BertsekasHeurCost G H j) m →
      ∀ i, m.head? = some i → (∀ v ∈ m.dropLast, v ∉ G.dest) →
      ∀ e, m.getLast? = some e → e ∈ G.dest →
      BertsekasHeurCost G H e = BertsekasHeurCost G H i +
        (m.dropLast.map (BertsekasRolloutDelta G H)).sum := by
    intro m
    induction m with
    | nil => intro _ i hi; simp at hi
    | cons a t ih =>
      intro hchain i hi hnodest e he hedest
      rcases t with _ | ⟨b, l'⟩
      · have hi' : a = i := by simpa using hi
        subst hi'
        have he' : a = e := by simpa using he
        subst he'
        simp
      · have hi' : a = i := by simpa using hi
        subst hi'
        obtain ⟨hRab, hchain'⟩ := List.isChain_cons_cons.mp hchain
        obtain ⟨hbmem, hbmin⟩ := hRab
        have hdrop : (a :: b :: l').dropLast = a :: (b :: l').dropLast := rfl
        have he' : (b :: l').getLast? = some e := he
        have hnodest' : ∀ v ∈ (b :: l').dropLast, v ∉ G.dest := fun v hv =>
          hnodest v (hdrop ▸ List.mem_cons_of_mem a hv)
        have hIH := ih hchain' b (by simp) hnodest' e he' hedest
        have hne : (BertsekasNbrs G a).Nonempty := ⟨b, hbmem⟩
        have hinf_le : (BertsekasNbrs G a).inf' hne (BertsekasHeurCost G H) ≤
            BertsekasHeurCost G H b := Finset.inf'_le _ hbmem
        have hle_inf : BertsekasHeurCost G H b ≤
            (BertsekasNbrs G a).inf' hne (BertsekasHeurCost G H) :=
          Finset.le_inf' _ _ hbmin
        have heq_inf : (BertsekasNbrs G a).inf' hne (BertsekasHeurCost G H) =
            BertsekasHeurCost G H b := le_antisymm hinf_le hle_inf
        have hdelta : BertsekasRolloutDelta G H a =
            BertsekasHeurCost G H b - BertsekasHeurCost G H a := by
          unfold BertsekasRolloutDelta
          rw [dif_pos hne, heq_inf]
        rw [hdrop, List.map_cons, List.sum_cons, hIH]
        linarith [hdelta]
  exact key l hchain i₁ hhead hnodest d hlast hdest'
