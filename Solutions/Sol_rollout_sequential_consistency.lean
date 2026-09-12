import Mathlib
import Definitions.Def_BertsekasGraphSearch

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasGraphSearch V) (H : BertsekasBaseHeuristic G)
    (hcons : BertsekasSeqConsistent G H)
    (r : ℕ → V) (hstart : r 0 ∉ G.dest)
    (hstep : ∀ k, r k ∉ G.dest →
      r (k + 1) ∈ BertsekasNbrs G (r k) ∧
      (∀ j ∈ BertsekasNbrs G (r k),
        BertsekasHeurCost G H (r (k + 1)) ≤ BertsekasHeurCost G H j))
    (htie : ∀ k, r k ∉ G.dest → ∀ (jH : V) (l : List V),
      H.path (r k) = r k :: jH :: l →
      (∀ j ∈ BertsekasNbrs G (r k),
        BertsekasHeurCost G H jH ≤ BertsekasHeurCost G H j) →
      r (k + 1) = jH)
    (habsorb : ∀ k, r k ∈ G.dest → r (k + 1) = r k) :
    (∃ K, r K ∈ G.dest) ∧
    (∀ K, r K ∈ G.dest →
      BertsekasHeurCost G H (r K) ≤ BertsekasHeurCost G H (r 0) ∧
      IsLeast {c : ℝ | c = BertsekasHeurCost G H (r 0) ∨
          ∃ k < K, r k ∉ G.dest ∧
            ∃ j ∈ BertsekasNbrs G (r k), c = BertsekasHeurCost G H j}
        (BertsekasHeurCost G H (r K))) := by
  have hpath_succ : ∀ i, i ∉ G.dest → ∃ jH l, H.path i = i :: jH :: l := by
    intro i hi
    obtain ⟨d, hd, hdl⟩ := H.hend i
    have hs := H.hstart i
    rcases hp : H.path i with _ | ⟨a, t⟩
    · rw [hp] at hs; simp at hs
    · have ha : a = i := by rw [hp] at hs; simpa using hs
      rcases t with _ | ⟨b, t'⟩
      · exfalso
        apply hi
        rw [hp] at hdl
        simp only [List.getLast?_singleton, Option.some.injEq] at hdl
        rw [← ha, hdl]; exact hd
      · refine ⟨b, t', ?_⟩
        rw [ha]
  have hgetD : ∀ (t : List V), t ≠ [] → ∀ d1 d2 : V,
      t.getLast?.getD d1 = t.getLast?.getD d2 := by
    intro t
    induction t with
    | nil => intro h; exact absurd rfl h
    | cons a t ih =>
      intro _ d1 d2
      rcases t with _ | ⟨b, t'⟩
      · rfl
      · rw [List.getLast?_cons_of_ne_nil (List.cons_ne_nil b t')]
        exact ih (List.cons_ne_nil b t') d1 d2
  have hHeq : ∀ i jH l, i ∉ G.dest → H.path i = i :: jH :: l →
      BertsekasHeurCost G H i = BertsekasHeurCost G H jH := by
    intro i jH l hi hp
    have hjHpath : H.path jH = jH :: l := hcons i hi jH l hp
    have hne : (jH :: l : List V) ≠ [] := List.cons_ne_nil jH l
    have hproj_eq : BertsekasProjection G H i = BertsekasProjection G H jH := by
      unfold BertsekasProjection
      rw [hp, hjHpath, List.getLast?_cons_of_ne_nil hne]
      exact hgetD (jH :: l) hne i jH
    unfold BertsekasHeurCost
    rw [hproj_eq]
  set ψ : V → ℕ := fun v =>
    (Finset.univ.filter (fun w => BertsekasHeurCost G H w < BertsekasHeurCost G H v)).card
    with hψdef
  have hψmono : ∀ a b : V, BertsekasHeurCost G H a < BertsekasHeurCost G H b → ψ a < ψ b := by
    intro a b hab
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (fun w hw => by
      simp only [hψdef, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact lt_trans hw hab)]
    exact ⟨a, by simp [hψdef, hab], by simp [hψdef]⟩
  set M : ℕ := Finset.univ.sup (fun v => (H.path v).length) with hMdef
  have hMbound : ∀ v, (H.path v).length ≤ M := by
    intro v; rw [hMdef]
    exact Finset.le_sup (f := fun v => (H.path v).length) (Finset.mem_univ v)
  set Φ : V → ℕ := fun v => ψ v * (M + 1) + (H.path v).length with hΦdef
  have hstepFacts : ∀ k, r k ∉ G.dest →
      BertsekasHeurCost G H (r (k + 1)) ≤ BertsekasHeurCost G H (r k) ∧
      Φ (r (k + 1)) < Φ (r k) := by
    intro k hk
    obtain ⟨jH, l, hp⟩ := hpath_succ (r k) hk
    have heqjH : BertsekasHeurCost G H (r k) = BertsekasHeurCost G H jH := hHeq (r k) jH l hk hp
    by_cases htieCase : ∀ j ∈ BertsekasNbrs G (r k),
        BertsekasHeurCost G H jH ≤ BertsekasHeurCost G H j
    · have hreq : r (k + 1) = jH := htie k hk jH l hp htieCase
      have hjHpath : H.path jH = jH :: l := hcons (r k) hk jH l hp
      have hHeqstep : BertsekasHeurCost G H (r (k + 1)) = BertsekasHeurCost G H (r k) := by
        rw [hreq]; exact heqjH.symm
      have hψeq : ψ (r (k + 1)) = ψ (r k) := by
        simp only [hψdef]; rw [hHeqstep]
      have hlen : (H.path (r (k + 1))).length < (H.path (r k)).length := by
        rw [hreq, hp, hjHpath]; simp
      refine ⟨le_of_eq hHeqstep, ?_⟩
      simp only [hΦdef]
      rw [hψeq]
      omega
    · push_neg at htieCase
      obtain ⟨j0, hj0mem, hj0lt⟩ := htieCase
      obtain ⟨hmem, hmin⟩ := hstep k hk
      have hlt1 : BertsekasHeurCost G H (r (k + 1)) ≤ BertsekasHeurCost G H j0 := hmin j0 hj0mem
      have hlt2 : BertsekasHeurCost G H (r (k + 1)) < BertsekasHeurCost G H (r k) := by
        rw [heqjH]; linarith [hlt1, hj0lt]
      refine ⟨le_of_lt hlt2, ?_⟩
      have hψlt : ψ (r (k + 1)) < ψ (r k) := hψmono _ _ hlt2
      have hlen1 : (H.path (r (k + 1))).length ≤ M := hMbound _
      have hlen2 : 0 ≤ (H.path (r k)).length := Nat.zero_le _
      simp only [hΦdef]
      nlinarith [hψlt, hlen1, hlen2]
  have hterm : ∃ K, r K ∈ G.dest := by
    by_contra hcon
    push_neg at hcon
    have hdecr : ∀ n, Φ (r n) + n ≤ Φ (r 0) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hstepn := (hstepFacts n (hcon n)).2
        omega
    have := hdecr (Φ (r 0) + 1)
    omega
  have hinv : ∀ K, BertsekasHeurCost G H (r K) ≤ BertsekasHeurCost G H (r 0) ∧
      IsLeast {c : ℝ | c = BertsekasHeurCost G H (r 0) ∨
          ∃ k < K, r k ∉ G.dest ∧ ∃ j ∈ BertsekasNbrs G (r k), c = BertsekasHeurCost G H j}
        (BertsekasHeurCost G H (r K)) := by
    intro K
    induction K with
    | zero =>
      refine ⟨le_refl _, ⟨Or.inl rfl, ?_⟩⟩
      intro c hc
      rcases hc with hc | ⟨k, hk, _, _⟩
      · exact le_of_eq hc.symm
      · exact absurd hk (Nat.not_lt_zero k)
    | succ K ih =>
      obtain ⟨ihle, ihleast⟩ := ih
      by_cases hKdest : r K ∈ G.dest
      · have hreq : r (K + 1) = r K := habsorb K hKdest
        rw [hreq]
        refine ⟨ihle, ⟨?_, ?_⟩⟩
        · rcases ihleast.1 with h | ⟨k, hk, hknd, j, hj, hc⟩
          · exact Or.inl h
          · exact Or.inr ⟨k, by omega, hknd, j, hj, hc⟩
        intro c hc
        apply ihleast.2
        rcases hc with hc | ⟨k, hk, hknd, j, hj, hc⟩
        · exact Or.inl hc
        · have hkK : k < K := by
            rcases (by omega : k < K ∨ k = K) with h | h
            · exact h
            · exact absurd (h ▸ hknd) (by simp [hKdest])
          exact Or.inr ⟨k, hkK, hknd, j, hj, hc⟩
      · obtain ⟨hHmono, _⟩ := hstepFacts K hKdest
        obtain ⟨hmem, hmin⟩ := hstep K hKdest
        refine ⟨le_trans hHmono ihle, ⟨?_, ?_⟩⟩
        · exact Or.inr ⟨K, Nat.lt_succ_self K, hKdest, r (K + 1), hmem, rfl⟩
        · intro c hc
          rcases hc with hc | ⟨k, hk, hknd, j, hj, hc⟩
          · rw [hc]; exact le_trans hHmono ihle
          · rcases (by omega : k < K ∨ k = K) with hlt | heq
            · have hcmem : c ∈ {c : ℝ | c = BertsekasHeurCost G H (r 0) ∨
                  ∃ k < K, r k ∉ G.dest ∧ ∃ j ∈ BertsekasNbrs G (r k),
                    c = BertsekasHeurCost G H j} := Or.inr ⟨k, hlt, hknd, j, hj, hc⟩
              exact le_trans hHmono (ihleast.2 hcmem)
            · subst heq
              rw [hc]
              exact hmin j hj
  exact ⟨hterm, fun K _ => hinv K⟩
