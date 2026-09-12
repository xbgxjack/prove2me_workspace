import Mathlib
import Definitions.Def_BertsekasDPModel
import Definitions.Def_BertsekasDPOpenLoopCost

theorem solution {S C W : Type} [Fintype W]
    (M : BertsekasDPModel S C W)
    (hUconst : ∀ k x x', M.U k x = M.U k x')
    (π : ℕ → S → C)
    (holfc : ∀ k, k < M.N → ∀ x, ∃ useq : ℕ → C,
      (∀ i, k ≤ i → i < M.N → useq i ∈ M.U i x) ∧
      π k x = useq k ∧
      (∀ useq' : ℕ → C, (∀ i, k ≤ i → i < M.N → useq' i ∈ M.U i x) →
        BertsekasDPOpenLoopCost M useq (M.N - k) x ≤
          BertsekasDPOpenLoopCost M useq' (M.N - k) x)) :
    ∀ (x₀ : S) (useq₀ : ℕ → C), (∀ i, i < M.N → useq₀ i ∈ M.U i x₀) →
      BertsekasDPPolicyCost M π M.N x₀ ≤
        BertsekasDPOpenLoopCost M useq₀ M.N x₀ := by
  have key : ∀ m, m ≤ M.N → ∀ x, ∀ useq : ℕ → C,
      (∀ i, M.N - m ≤ i → i < M.N → useq i ∈ M.U i x) →
      BertsekasDPPolicyCost M π m x ≤ BertsekasDPOpenLoopCost M useq m x := by
    intro m
    induction m with
    | zero =>
      intro _ x useq _
      simp only [BertsekasDPPolicyCost, BertsekasDPOpenLoopCost]
      exact le_refl _
    | succ m ih =>
      intro hm x useq hadm
      have hmN : m ≤ M.N := by omega
      have hklt : M.N - (m + 1) < M.N := by omega
      have hkey1 : M.N - (m + 1) + 1 = M.N - m := by omega
      have hNk : M.N - (M.N - (m + 1)) = m + 1 := by omega
      obtain ⟨useqx, hadmx, hπeq, hopt⟩ := holfc (M.N - (m + 1)) hklt x
      have hopt' := hopt useq (by
        intro i hi hiN
        exact hadm i (by omega) hiN)
      rw [hNk] at hopt'
      have hstepPolicy : BertsekasDPPolicyCost M π (m + 1) x =
          ∑ w, M.p (M.N - (m + 1)) x (useqx (M.N - (m + 1))) w *
            (M.g (M.N - (m + 1)) x (useqx (M.N - (m + 1))) w +
              BertsekasDPPolicyCost M π m
                (M.f (M.N - (m + 1)) x (useqx (M.N - (m + 1))) w)) := by
        simp only [BertsekasDPPolicyCost, hπeq]
      have hstepOpen : BertsekasDPOpenLoopCost M useqx (m + 1) x =
          ∑ w, M.p (M.N - (m + 1)) x (useqx (M.N - (m + 1))) w *
            (M.g (M.N - (m + 1)) x (useqx (M.N - (m + 1))) w +
              BertsekasDPOpenLoopCost M useqx m
                (M.f (M.N - (m + 1)) x (useqx (M.N - (m + 1))) w)) := by
        simp only [BertsekasDPOpenLoopCost]
      have hbound : BertsekasDPPolicyCost M π (m + 1) x ≤
          BertsekasDPOpenLoopCost M useqx (m + 1) x := by
        rw [hstepPolicy, hstepOpen]
        apply Finset.sum_le_sum
        intro w _
        have hmem : useqx (M.N - (m + 1)) ∈
            M.U (M.N - (m + 1)) x := hadmx (M.N - (m + 1)) (le_refl _) hklt
        have hpnn : 0 ≤ M.p (M.N - (m + 1)) x (useqx (M.N - (m + 1))) w :=
          M.hp_nonneg _ x _ hmem w
        have hadmx' : ∀ i, M.N - m ≤ i → i < M.N →
            useqx i ∈ M.U i (M.f (M.N - (m + 1)) x (useqx (M.N - (m + 1))) w) := by
          intro i hi hiN
          rw [hUconst i (M.f (M.N - (m + 1)) x (useqx (M.N - (m + 1))) w) x]
          exact hadmx i (by omega) hiN
        have hIH := ih hmN (M.f (M.N - (m + 1)) x (useqx (M.N - (m + 1))) w) useqx hadmx'
        gcongr
      calc BertsekasDPPolicyCost M π (m + 1) x
          ≤ BertsekasDPOpenLoopCost M useqx (m + 1) x := hbound
        _ ≤ BertsekasDPOpenLoopCost M useq (m + 1) x := hopt'
  intro x₀ useq₀ hadm₀
  have := key M.N (le_refl _) x₀ useq₀ (by
    intro i _ hiN
    exact hadm₀ i hiN)
  simpa using this
