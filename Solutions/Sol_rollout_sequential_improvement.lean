import Mathlib
import Definitions.Def_BertsekasGraphSearch

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasGraphSearch V) (H : BertsekasBaseHeuristic G)
    (himp : BertsekasSeqImproving G H)
    (l : List V) (hrun : BertsekasIsRolloutRun G H l)
    (i₁ : V) (hhead : l.head? = some i₁) (hstart : i₁ ∉ G.dest)
    (d : V) (hlast : l.getLast? = some d) :
    G.cost d ≤ BertsekasHeurCost G H i₁ ∧
    IsLeast {c : ℝ | c = BertsekasHeurCost G H i₁ ∨
        ∃ v ∈ l.dropLast, ∃ j ∈ BertsekasNbrs G v, c = BertsekasHeurCost G H j}
      (G.cost d) := by
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
  have hdelta_nonpos : ∀ v, v ∉ G.dest → BertsekasRolloutDelta G H v ≤ 0 := by
    intro v hv
    unfold BertsekasRolloutDelta
    split
    · rename_i hne
      linarith [himp v hv hne]
    · linarith
  have key : ∀ (m : List V), List.IsChain (fun a b => b ∈ BertsekasNbrs G a ∧
        ∀ j ∈ BertsekasNbrs G a, BertsekasHeurCost G H b ≤ BertsekasHeurCost G H j) m →
      ∀ i, m.head? = some i → (∀ v ∈ m.dropLast, v ∉ G.dest) →
      ∀ e, m.getLast? = some e → e ∈ G.dest →
      BertsekasHeurCost G H e ≤ BertsekasHeurCost G H i ∧
      IsLeast {c : ℝ | c = BertsekasHeurCost G H i ∨
          ∃ v ∈ m.dropLast, ∃ j ∈ BertsekasNbrs G v, c = BertsekasHeurCost G H j}
        (BertsekasHeurCost G H e) := by
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
        refine ⟨le_refl _, ⟨Or.inl rfl, ?_⟩⟩
        intro c hc
        rcases hc with hc | ⟨v, hv, j, hj, hc⟩
        · exact le_of_eq hc.symm
        · simp at hv
      · have hi' : a = i := by simpa using hi
        subst hi'
        obtain ⟨hRab, hchain'⟩ := List.isChain_cons_cons.mp hchain
        obtain ⟨hbmem, hbmin⟩ := hRab
        have hdrop : (a :: b :: l').dropLast = a :: (b :: l').dropLast := rfl
        have he' : (b :: l').getLast? = some e := he
        have hnodest' : ∀ v ∈ (b :: l').dropLast, v ∉ G.dest := fun v hv =>
          hnodest v (hdrop ▸ List.mem_cons_of_mem a hv)
        have ha_notdest : a ∉ G.dest := hnodest a (hdrop ▸ List.mem_cons_self)
        obtain ⟨hIHle, hIHleast⟩ := ih hchain' b (by simp) hnodest' e he' hedest
        have hne : (BertsekasNbrs G a).Nonempty := ⟨b, hbmem⟩
        have hinf_le : (BertsekasNbrs G a).inf' hne (BertsekasHeurCost G H) ≤
            BertsekasHeurCost G H b := Finset.inf'_le _ hbmem
        have hle_inf : BertsekasHeurCost G H b ≤
            (BertsekasNbrs G a).inf' hne (BertsekasHeurCost G H) :=
          Finset.le_inf' _ _ hbmin
        have heq_inf : (BertsekasNbrs G a).inf' hne (BertsekasHeurCost G H) =
            BertsekasHeurCost G H b := le_antisymm hinf_le hle_inf
        have hdelta_le : BertsekasRolloutDelta G H a ≤ 0 := hdelta_nonpos a ha_notdest
        have hdelta_eq : BertsekasRolloutDelta G H a =
            BertsekasHeurCost G H b - BertsekasHeurCost G H a := by
          unfold BertsekasRolloutDelta
          rw [dif_pos hne, heq_inf]
        have hba : BertsekasHeurCost G H b ≤ BertsekasHeurCost G H a := by
          linarith [hdelta_le, hdelta_eq]
        have heIHmem := hIHleast.1
        have heIHlb := hIHleast.2
        have heb : BertsekasHeurCost G H e ≤ BertsekasHeurCost G H b := heIHlb (Or.inl rfl)
        refine ⟨by linarith [heb, hba], ⟨?_, ?_⟩⟩
        · rcases heIHmem with hm | ⟨v, hv, j, hj, hm⟩
          · exact Or.inr ⟨a, hdrop ▸ List.mem_cons_self, b, hbmem, hm⟩
          · exact Or.inr ⟨v, hdrop ▸ List.mem_cons_of_mem a hv, j, hj, hm⟩
        · intro c hc
          rcases hc with hc | ⟨v, hv, j, hj, hc⟩
          · subst hc
            linarith [heb, hba]
          · rw [hdrop] at hv
            rcases List.mem_cons.mp hv with hv | hv
            · subst hv
              have hbj : BertsekasHeurCost G H b ≤ BertsekasHeurCost G H j := hbmin j hj
              subst hc
              linarith [heb, hbj]
            · have hctail : c ∈ {c : ℝ | c = BertsekasHeurCost G H b ∨
                  ∃ v ∈ (b :: l').dropLast, ∃ j ∈ BertsekasNbrs G v,
                    c = BertsekasHeurCost G H j} :=
                Or.inr ⟨v, hv, j, hj, hc⟩
              exact heIHlb hctail
  obtain ⟨hle, hleast⟩ := key l hchain i₁ hhead hnodest d hlast hdest'
  rw [hHeurEq] at hle hleast
  exact ⟨hle, hleast⟩
