import Mathlib
import Theorems.Thm_Erdos287_block_theorem

open Finset

/-- **The gap-two bound for Erdős Problem 287.** In every representation of `1` as a sum of
`k ≥ 2` reciprocals of strictly increasing integers greater than `1`, some consecutive gap is
at least `2`. Equivalently: the denominators can never form a block of consecutive integers,
which is exactly Kürschák's block theorem. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) :
    ∃ i, i + 1 < k ∧ 2 ≤ f (i + 1) - f i := by
  by_contra hcon
  push_neg at hcon
  -- every gap is exactly one, so `f` is an arithmetic progression of step one on the window
  have hstep : ∀ i, i + 1 < k → f (i + 1) = f i + 1 := by
    intro i hi
    have h1 : f i < f (i + 1) := hmono i (i + 1) (by omega) hi
    have h2 : f (i + 1) - f i < 2 := hcon i hi
    omega
  have hform : ∀ i, i < k → f i = f 0 + i := by
    intro i hi
    induction i with
    | zero => simp
    | succ j ih =>
      have hj : j < k := by omega
      rw [hstep j (by omega), ih hj]
      omega
  -- so the sum is a block of consecutive reciprocals equal to `1`
  have hrw : ∑ i ∈ Finset.range k, (1 : ℚ) / f i
      = ∑ i ∈ Finset.range k, (1 : ℚ) / ((f 0 : ℚ) + (i : ℚ)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hform i (Finset.mem_range.mp hi)]
    push_cast; ring
  rw [hrw] at hsum
  have hf0 : 0 < f 0 := by have := hf1 0 (by omega); omega
  exact Erdos287.block_theorem (f 0) k hf0 hk ⟨1, by rw [hsum]; norm_num⟩
