import Mathlib

open Finset

noncomputable def katonaBound (n t : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc ((n + t) / 2) n, n.choose i

/-- Pascal's identity telescopes the two smaller Katona bounds into the bigger one. -/
theorem katonaBound_pascal {n t : ℕ} (ht1 : 1 ≤ t) (htn : t < n) (h2 : 2 ∣ (n + t)) :
    katonaBound (n - 1) (t - 1) + katonaBound (n - 1) (t + 1) = katonaBound n t := by
  obtain ⟨k, hk⟩ := h2
  have hn1 : 1 ≤ n := by omega
  have e1 : (n + t) / 2 = k := by omega
  have e2 : ((n - 1) + (t - 1)) / 2 = k - 1 := by omega
  have e3 : ((n - 1) + (t + 1)) / 2 = k := by omega
  unfold katonaBound
  rw [e1, e2, e3]
  have hk1 : 1 ≤ k := by omega
  have hkn : k ≤ n - 1 := by omega
  set S := ∑ i ∈ Finset.Icc k (n - 1), (n - 1).choose i with hS_def
  set T := ∑ i ∈ Finset.Icc (k - 1) (n - 2), (n - 1).choose i with hT_def
  -- F1: split `Icc (k-1) (n-1)` at its bottom element `k-1`.
  have hsplit1 : Finset.Icc (k - 1) (n - 1) = insert (k - 1) (Finset.Icc k (n - 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have F1 : ∑ i ∈ Finset.Icc (k - 1) (n - 1), (n - 1).choose i = (n - 1).choose (k - 1) + S := by
    rw [hsplit1, Finset.sum_insert (by simp; omega)]
  -- F2: split `Icc (k-1) (n-1)` at its top element `n-1`.
  have hIcc_split : Finset.Icc (k - 1) (n - 1) = insert (n - 1) (Finset.Icc (k - 1) (n - 2)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have F2 : ∑ i ∈ Finset.Icc (k - 1) (n - 1), (n - 1).choose i = 1 + T := by
    rw [hIcc_split, Finset.sum_insert (by simp; omega), Nat.choose_self]
  -- F3: split `Icc k n` at its top element `n`.
  have hpascal : Finset.Icc k n = insert n (Finset.Icc k (n - 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have F3 : ∑ i ∈ Finset.Icc k n, n.choose i = 1 + ∑ i ∈ Finset.Icc k (n - 1), n.choose i := by
    rw [hpascal, Finset.sum_insert (by simp; omega), Nat.choose_self]
  -- F4: apply Pascal's rule termwise, then reindex the shadow sum onto `T`.
  have hterm : ∀ i ∈ Finset.Icc k (n - 1),
      n.choose i = (n - 1).choose (i - 1) + (n - 1).choose i := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi1 : 1 ≤ i := by omega
    have hp := Nat.choose_succ_succ (n - 1) (i - 1)
    simp only [Nat.succ_eq_add_one] at hp
    rw [Nat.sub_add_cancel hn1, Nat.sub_add_cancel hi1] at hp
    exact hp
  have hreindex : ∑ i ∈ Finset.Icc k (n - 1), (n - 1).choose (i - 1) = T := by
    rw [hT_def]
    apply Finset.sum_nbij' (fun i => i - 1) (fun i => i + 1)
    · intro i hi; rw [Finset.mem_Icc] at hi ⊢; omega
    · intro i hi; rw [Finset.mem_Icc] at hi ⊢; omega
    · intro i hi; rw [Finset.mem_Icc] at hi; omega
    · intro i hi; rw [Finset.mem_Icc] at hi; omega
    · intro i hi; rfl
  have F4 : ∑ i ∈ Finset.Icc k (n - 1), n.choose i = T + S := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hreindex, hS_def]
  rw [F1, F3, F4]
  omega
