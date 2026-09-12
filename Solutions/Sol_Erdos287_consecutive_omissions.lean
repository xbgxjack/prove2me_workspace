import Mathlib

open Finset

/-- If two consecutive integers inside the range of the denominators are both missing from the
list, then some consecutive gap is at least `3`. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (x : ℕ) (hx0 : f 0 ≤ x) (hx1 : x + 1 ≤ f (k - 1))
    (hmiss : ∀ i, i < k → f i ≠ x) (hmiss' : ∀ i, i < k → f i ≠ x + 1) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  classical
  set A : Finset ℕ := (Finset.range k).filter (fun j => f j < x) with hA
  have h0A : 0 ∈ A := by
    rw [hA, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, lt_of_le_of_ne hx0 (hmiss 0 (by omega))⟩
  have hne : A.Nonempty := ⟨0, h0A⟩
  set i := A.max' hne with hi
  have hiA : i ∈ A := A.max'_mem hne
  have hmem := Finset.mem_filter.mp hiA
  have hik : i < k := Finset.mem_range.mp hmem.1
  have hfi : f i < x := hmem.2
  have hlast : k - 1 ∉ A := by
    intro h
    have := (Finset.mem_filter.mp h).2
    omega
  have hik1 : i + 1 < k := by
    rcases Nat.lt_or_ge i (k - 1) with h | h
    · omega
    · exfalso
      apply hlast
      have hik' : i = k - 1 := by omega
      rwa [hik'] at hiA
  have hnext : ¬ (f (i + 1) < x) := by
    intro h
    have hmemA : i + 1 ∈ A := by
      rw [hA, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, h⟩
    have := A.le_max' _ hmemA
    omega
  have h1 : f (i + 1) ≠ x := hmiss _ hik1
  have h2 : f (i + 1) ≠ x + 1 := hmiss' _ hik1
  exact ⟨i, hik1, by omega⟩
