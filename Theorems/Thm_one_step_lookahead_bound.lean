import Mathlib
import Definitions.Def_BertsekasDPModel
namespace BertsekasDP

theorem one_step_lookahead_bound {S C W : Type} [Fintype W]
    (M : BertsekasDPModel S C W)
    (Jt : ℕ → S → ℝ) (hJN : ∀ x, Jt M.N x = M.gN x)
    (Ubar : ℕ → S → Finset C)
    (hUsub : ∀ k x, Ubar k x ⊆ M.U k x)
    (π : ℕ → S → C)
    (hπmem : ∀ k x, π k x ∈ Ubar k x)
    (hπmin : ∀ k, k < M.N → ∀ x, ∀ u ∈ Ubar k x,
      ∑ w, M.p k x (π k x) w *
          (M.g k x (π k x) w + Jt (k + 1) (M.f k x (π k x) w)) ≤
        ∑ w, M.p k x u w * (M.g k x u w + Jt (k + 1) (M.f k x u w)))
    (h620 : ∀ k, k < M.N → ∀ x,
      ∑ w, M.p k x (π k x) w *
          (M.g k x (π k x) w + Jt (k + 1) (M.f k x (π k x) w)) ≤ Jt k x) :
    ∀ k, k ≤ M.N → ∀ x,
      (k < M.N →
        BertsekasDPPolicyCost M π (M.N - k) x ≤
          ∑ w, M.p k x (π k x) w *
            (M.g k x (π k x) w + Jt (k + 1) (M.f k x (π k x) w))) ∧
      BertsekasDPPolicyCost M π (M.N - k) x ≤ Jt k x := by
  have key : ∀ m, m ≤ M.N → ∀ x,
      (m > 0 →
        BertsekasDPPolicyCost M π m x ≤
          ∑ w, M.p (M.N - m) x (π (M.N - m) x) w *
            (M.g (M.N - m) x (π (M.N - m) x) w +
              Jt (M.N - m + 1) (M.f (M.N - m) x (π (M.N - m) x) w))) ∧
      BertsekasDPPolicyCost M π m x ≤ Jt (M.N - m) x := by
    intro m
    induction m with
    | zero =>
      intro _ x
      refine ⟨fun h => absurd h (lt_irrefl 0), ?_⟩
      simp only [BertsekasDPPolicyCost, Nat.sub_zero, hJN, le_refl]
    | succ m ih =>
      intro hm x
      have hmN : m ≤ M.N := by omega
      have hklt : M.N - (m + 1) < M.N := by omega
      have hkey1 : M.N - (m + 1) + 1 = M.N - m := by omega
      have hmem : π (M.N - (m + 1)) x ∈ M.U (M.N - (m + 1)) x :=
        hUsub _ x (hπmem _ x)
      have hpnn : ∀ w, 0 ≤ M.p (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w :=
        fun w => M.hp_nonneg _ x _ hmem w
      have hstep : BertsekasDPPolicyCost M π (m + 1) x =
          ∑ w, M.p (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w *
            (M.g (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w +
              BertsekasDPPolicyCost M π m
                (M.f (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w)) := by
        simp only [BertsekasDPPolicyCost]
      have hbound : BertsekasDPPolicyCost M π (m + 1) x ≤
          ∑ w, M.p (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w *
            (M.g (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w +
              Jt (M.N - (m + 1) + 1) (M.f (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w)) := by
        rw [hstep]
        apply Finset.sum_le_sum
        intro w _
        have hIH := (ih hmN (M.f (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w)).2
        rw [← hkey1] at hIH
        gcongr
        exact hpnn w
      refine ⟨fun _ => hbound, ?_⟩
      have h620' := h620 (M.N - (m + 1)) hklt x
      calc BertsekasDPPolicyCost M π (m + 1) x
          ≤ _ := hbound
        _ ≤ Jt (M.N - (m + 1)) x := h620'
  intro k hk x
  have hh := key (M.N - k) (by omega) x
  have hsub : M.N - (M.N - k) = k := by omega
  rw [hsub] at hh
  exact ⟨fun hklt => hh.1 (by omega), hh.2⟩

end BertsekasDP
