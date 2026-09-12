import Mathlib

open Finset

variable {γ : Type*} [Fintype γ]

theorem solution (p q : γ → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hpq : ∀ x, p x ≠ 0 → q x ≠ 0)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    ∑ x ∈ univ.filter (fun x => p x ≠ 0), p x * Real.log (q x / p x) ≤ 0 := by
  set S := univ.filter (fun x => p x ≠ 0) with hS_def
  have hpsumS : ∑ x ∈ S, p x = 1 := by
    rw [← hpsum, hS_def]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x _ hx
    simp only [Finset.mem_filter, mem_univ, true_and, not_not] at hx
    exact hx
  have hterm : ∀ x ∈ S, p x * Real.log (q x / p x) ≤ q x - p x := by
    intro x hx
    simp only [hS_def, Finset.mem_filter] at hx
    have hpxpos : 0 < p x := lt_of_le_of_ne (hp0 x) (Ne.symm hx.2)
    have hqxpos : 0 < q x := lt_of_le_of_ne (hq0 x) (Ne.symm (hpq x hx.2))
    have hlog : Real.log (q x / p x) ≤ q x / p x - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hqxpos hpxpos)
    calc p x * Real.log (q x / p x) ≤ p x * (q x / p x - 1) :=
          mul_le_mul_of_nonneg_left hlog (hp0 x)
      _ = q x - p x := by field_simp
  have hqsumS : ∑ x ∈ S, q x ≤ ∑ x, q x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro x _ _
    exact hq0 x
  calc ∑ x ∈ S, p x * Real.log (q x / p x)
      ≤ ∑ x ∈ S, (q x - p x) := Finset.sum_le_sum hterm
    _ = (∑ x ∈ S, q x) - ∑ x ∈ S, p x := by rw [Finset.sum_sub_distrib]
    _ ≤ (∑ x, q x) - ∑ x ∈ S, p x := by linarith
    _ = 1 - 1 := by rw [hqsum, hpsumS]
    _ = 0 := by ring
