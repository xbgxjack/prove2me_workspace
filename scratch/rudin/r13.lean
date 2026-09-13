import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

private lemma l2norm_eq {X : Type*} [MeasurableSpace X] {μ : Measure X} {h : X → ℝ}
    (hh : MemLp h 2 μ) : Rudin.L2Norm μ h = (eLpNorm h 2 μ).toReal := by
  rw [hh.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have hint : (∫ a, ‖h a‖ ^ (2:ℝ) ∂μ) = ∫ a, h a ^ 2 ∂μ := by
    congr 1
    funext a
    rw [show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  rw [hint]
  have hnn : (0:ℝ) ≤ ∫ a, h a ^ 2 ∂μ := integral_nonneg fun a => sq_nonneg _
  rw [Rudin.L2Norm, Real.sqrt_eq_rpow, ENNReal.toReal_ofReal (by positivity)]
  norm_num

example (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : Rudin.MemL2 (volume.restrict (Set.Icc a b)) f) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, Continuous g ∧
      Rudin.L2Norm (volume.restrict (Set.Icc a b)) (fun x => f x - g x) < ε := by
  set μ : Measure ℝ := volume.restrict (Set.Icc a b) with hμ
  have hfLp : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq hf.1.aestronglyMeasurable).mpr hf.2
  obtain ⟨g, hgle, hgLp⟩ :=
    hfLp.exists_boundedContinuous_eLpNorm_sub_le (p := 2) (by norm_num)
      (ε := ENNReal.ofReal (ε / 2)) (by simp [hε])
  refine ⟨g, g.continuous, ?_⟩
  have hml : MemLp (fun x => f x - g x) 2 μ := hfLp.sub hgLp
  rw [l2norm_eq hml]
  have hcong : eLpNorm (fun x => f x - g x) 2 μ = eLpNorm (f - (g : ℝ → ℝ)) 2 μ := by
    congr 1
  rw [hcong]
  have : (eLpNorm (f - (g : ℝ → ℝ)) 2 μ).toReal ≤ ε / 2 := by
    have h1 := ENNReal.toReal_mono (by simp) hgle
    rwa [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ ε / 2)] at h1
  linarith
