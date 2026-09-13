import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

set_option maxHeartbeats 1000000

private lemma summable_of_seriesConvergesTo_nonneg {u : ℕ → ℝ} {L : ℝ}
    (hnn : ∀ n, 0 ≤ u n) (h : Rudin.SeriesConvergesTo u L) : Summable u ∧ ∑' n, u n = L := by
  have hmono : Monotone (Rudin.partialSum u) := by
    intro m n hmn
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hnn i)
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hle : ∀ n, Rudin.partialSum u n ≤ L := hmono.ge_of_tendsto h
  have hsum : Summable u := summable_of_sum_range_le hnn hle
  refine ⟨hsum, ?_⟩
  exact tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat h

theorem solution (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hb : ∀ i, Rudin.SeriesConvergesTo (fun j => |a i j|) (b i))
    (hbsum : Rudin.SeriesConverges b) :
    ∃ S : ℝ,
      Rudin.SeriesConvergesTo (fun i => ∑' j, a i j) S ∧
      Rudin.SeriesConvergesTo (fun j => ∑' i, a i j) S := by
  have hrow : ∀ i, Summable (fun j => |a i j|) ∧ ∑' j, |a i j| = b i := fun i =>
    summable_of_seriesConvergesTo_nonneg (fun j => abs_nonneg _) (hb i)
  have hbnn : ∀ i, 0 ≤ b i := fun i => (hrow i).2 ▸ tsum_nonneg fun j => abs_nonneg _
  obtain ⟨sb, hsb⟩ := hbsum
  have hbS : Summable b := (summable_of_seriesConvergesTo_nonneg hbnn hsb).1
  have habs : Summable (fun p : ℕ × ℕ => |a p.1 p.2|) := by
    rw [summable_prod_of_nonneg (fun p => abs_nonneg _)]
    refine ⟨fun i => (hrow i).1, ?_⟩
    have he : (fun i => ∑' j, |a i j|) = b := funext fun i => (hrow i).2
    rw [he]; exact hbS
  have hprod : Summable (fun p : ℕ × ℕ => a p.1 p.2) :=
    Summable.of_norm_bounded habs (fun p => le_of_eq (Real.norm_eq_abs _))
  have hrowsum : ∀ i, Summable (fun j => a i j) := fun i =>
    Summable.of_norm_bounded (hrow i).1 (fun j => le_of_eq (Real.norm_eq_abs _))
  have habs' : Summable (fun p : ℕ × ℕ => |a p.2 p.1|) := habs.prod_symm
  have hcolabs : ∀ j, Summable (fun i => |a i j|) :=
    fun j => ((summable_prod_of_nonneg (fun p : ℕ × ℕ => abs_nonneg (a p.2 p.1))).mp habs').1 j
  have hcolsum : ∀ j, Summable (fun i => a i j) := fun j =>
    Summable.of_norm_bounded (hcolabs j) (fun i => le_of_eq (Real.norm_eq_abs _))
  have hcolb : Summable (fun j => ∑' i, |a i j|) :=
    ((summable_prod_of_nonneg (fun p : ℕ × ℕ => abs_nonneg (a p.2 p.1))).mp habs').2
  have hS1 : Summable (fun i => ∑' j, a i j) := by
    refine Summable.of_norm_bounded hbS (fun i => ?_)
    rw [← (hrow i).2]
    have h1 : Summable (fun j => ‖a i j‖) := by simpa [Real.norm_eq_abs] using (hrow i).1
    calc ‖∑' j, a i j‖ ≤ ∑' j, ‖a i j‖ := norm_tsum_le_tsum_norm h1
      _ = ∑' j, |a i j| := by simp [Real.norm_eq_abs]
  have hS2 : Summable (fun j => ∑' i, a i j) := by
    refine Summable.of_norm_bounded hcolb (fun j => ?_)
    have h1 : Summable (fun i => ‖a i j‖) := by simpa [Real.norm_eq_abs] using (hcolabs j)
    calc ‖∑' i, a i j‖ ≤ ∑' i, ‖a i j‖ := norm_tsum_le_tsum_norm h1
      _ = ∑' i, |a i j| := by simp [Real.norm_eq_abs]
  have heq1 : ∑' p : ℕ × ℕ, a p.1 p.2 = ∑' i, ∑' j, a i j := hprod.tsum_prod' hrowsum
  have heq2 : ∑' j, ∑' i, a i j = ∑' i, ∑' j, a i j :=
    Summable.tsum_comm' hprod hrowsum hcolsum
  refine ⟨∑' p : ℕ × ℕ, a p.1 p.2, ?_, ?_⟩
  · rw [heq1]; exact hS1.hasSum.tendsto_sum_nat
  · rw [heq1, ← heq2]; exact hS2.hasSum.tendsto_sum_nat
