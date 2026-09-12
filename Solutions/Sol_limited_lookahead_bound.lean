import Mathlib
import Definitions.Def_BertsekasDPModel

theorem solution {S C W : Type} [Fintype W]
    (M : BertsekasDPModel S C W)
    (Jt : ℕ → S → ℝ) (hJN : ∀ x, Jt M.N x = M.gN x)
    (δ : ℕ → ℝ)
    (π : ℕ → S → C)
    (hadm : ∀ k x, π k x ∈ M.U k x)
    (hπ : ∀ k, k < M.N → ∀ x,
      ∑ w, M.p k x (π k x) w *
          (M.g k x (π k x) w + Jt (k + 1) (M.f k x (π k x) w)) ≤
        Jt k x + δ k) :
    ∀ k, k ≤ M.N → ∀ x,
      BertsekasDPPolicyCost M π (M.N - k) x ≤
        Jt k x + ∑ i ∈ Finset.Ico k M.N, δ i := by
  have hSstep : ∀ k, k < M.N →
      (∑ i ∈ Finset.Ico k M.N, δ i) = δ k + ∑ i ∈ Finset.Ico (k + 1) M.N, δ i := by
    intro k hk
    have hsplit := Finset.sum_Ico_consecutive δ (Nat.le_succ k) hk
    rw [← hsplit]
    have hsingle : Finset.Ico k (k + 1) = {k} := by ext y; simp
    rw [hsingle, Finset.sum_singleton]
  have key : ∀ m, m ≤ M.N → ∀ x,
      BertsekasDPPolicyCost M π m x ≤
        Jt (M.N - m) x + ∑ i ∈ Finset.Ico (M.N - m) M.N, δ i := by
    intro m
    induction m with
    | zero =>
      intro _ x
      simp only [BertsekasDPPolicyCost, Nat.sub_zero, Finset.Ico_self, Finset.sum_empty,
        add_zero, hJN]
      exact le_refl _

    | succ m ih =>
      intro hm x
      have hmN : m ≤ M.N := by omega
      have hklt : M.N - (m + 1) < M.N := by omega
      have hkey1 : M.N - (m + 1) + 1 = M.N - m := by omega
      have hmem : π (M.N - (m + 1)) x ∈ M.U (M.N - (m + 1)) x := hadm _ x
      have hpnn : ∀ w, 0 ≤ M.p (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w :=
        fun w => M.hp_nonneg _ x _ hmem w
      have hpsum : ∑ w, M.p (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w = 1 :=
        M.hp_sum _ x _ hmem
      have hstep : BertsekasDPPolicyCost M π (m + 1) x =
          ∑ w, M.p (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w *
            (M.g (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w +
              BertsekasDPPolicyCost M π m
                (M.f (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w)) := by
        simp only [BertsekasDPPolicyCost]
      have hbound1 : BertsekasDPPolicyCost M π (m + 1) x ≤
          ∑ w, M.p (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w *
            (M.g (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w +
              (Jt (M.N - (m + 1) + 1) (M.f (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w) +
                ∑ i ∈ Finset.Ico (M.N - (m + 1) + 1) M.N, δ i)) := by
        rw [hstep]
        apply Finset.sum_le_sum
        intro w _
        have hIH := ih hmN (M.f (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w)
        rw [← hkey1] at hIH
        gcongr
        exact hpnn w
      have hrearrange : ∑ w, M.p (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w *
            (M.g (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w +
              (Jt (M.N - (m + 1) + 1) (M.f (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w) +
                ∑ i ∈ Finset.Ico (M.N - (m + 1) + 1) M.N, δ i)) =
          (∑ w, M.p (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w *
            (M.g (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w +
              Jt (M.N - (m + 1) + 1) (M.f (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w))) +
          ∑ i ∈ Finset.Ico (M.N - (m + 1) + 1) M.N, δ i := by
        have step1 : ∀ w, M.p (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w *
              (M.g (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w +
                (Jt (M.N - (m + 1) + 1) (M.f (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w) +
                  ∑ i ∈ Finset.Ico (M.N - (m + 1) + 1) M.N, δ i)) =
            M.p (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w *
              (M.g (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w +
                Jt (M.N - (m + 1) + 1) (M.f (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w)) +
            M.p (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w *
              ∑ i ∈ Finset.Ico (M.N - (m + 1) + 1) M.N, δ i := by
          intro w; ring
        rw [Finset.sum_congr rfl (fun w _ => step1 w), Finset.sum_add_distrib,
          ← Finset.sum_mul, hpsum, one_mul]
      rw [hrearrange] at hbound1
      have hπ' := hπ (M.N - (m + 1)) hklt x
      have hSsplit := hSstep (M.N - (m + 1)) hklt
      calc BertsekasDPPolicyCost M π (m + 1) x
          ≤ _ := hbound1
        _ ≤ (Jt (M.N - (m + 1)) x + δ (M.N - (m + 1))) +
              ∑ i ∈ Finset.Ico (M.N - (m + 1) + 1) M.N, δ i := by linarith [hπ']
        _ = Jt (M.N - (m + 1)) x + ∑ i ∈ Finset.Ico (M.N - (m + 1)) M.N, δ i := by
              rw [hSsplit]; ring
  intro k hk x
  have hh := key (M.N - k) (by omega) x
  have hsub : M.N - (M.N - k) = k := by omega
  rwa [hsub] at hh
