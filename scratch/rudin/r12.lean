import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

variable {X : Type*} [MeasurableSpace X]

private lemma l2norm_eq {μ : Measure X} {h : X → ℝ} (hh : MemLp h 2 μ) :
    Rudin.L2Norm μ h = (eLpNorm h 2 μ).toReal := by
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

example (μ : Measure X) (f : ℕ → X → ℝ)
    (hmem : ∀ n, Rudin.MemL2 μ (f n)) (hcauchy : Rudin.CauchyL2 μ f) :
    ∃ g : X → ℝ, Rudin.MemL2 μ g ∧ Rudin.TendstoL2 μ f g := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hLp : ∀ n, MemLp (f n) 2 μ := fun n =>
    (memLp_two_iff_integrable_sq (hmem n).1.aestronglyMeasurable).mpr (hmem n).2
  set F : ℕ → Lp ℝ 2 μ := fun n => (hLp n).toLp (f n) with hFdef
  have hcoe : ∀ n, (F n : X → ℝ) =ᵐ[μ] f n := fun n => MemLp.coeFn_toLp (hLp n)
  have hdist : ∀ m n, dist (F m) (F n) = Rudin.L2Norm μ (fun x => f m x - f n x) := by
    intro m n
    have hml : MemLp (fun x => f m x - f n x) 2 μ := (hLp m).sub (hLp n)
    rw [Lp.dist_def, l2norm_eq hml]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [hcoe m, hcoe n] with x hx hy
    simp [hx, hy]
  have hcs : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    exact ⟨N, fun m hm n hn => by rw [hdist m n]; exact hN n hn m hm⟩
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcs
  -- a strongly measurable representative of the limit
  have hGm := Lp.aestronglyMeasurable G
  set g : X → ℝ := hGm.mk (G : X → ℝ) with hgdef
  have hgsm : StronglyMeasurable g := hGm.stronglyMeasurable_mk
  have hgae : (G : X → ℝ) =ᵐ[μ] g := hGm.ae_eq_mk
  have hgLp : MemLp g 2 μ := (Lp.memLp G).ae_eq hgae
  refine ⟨g, ⟨hgsm.measurable, (memLp_two_iff_integrable_sq hgsm.aestronglyMeasurable).mp hgLp⟩, ?_⟩
  have hdist2 : ∀ n, dist (F n) G = Rudin.L2Norm μ (fun x => f n x - g x) := by
    intro n
    have hml : MemLp (fun x => f n x - g x) 2 μ := (hLp n).sub hgLp
    rw [Lp.dist_def, l2norm_eq hml]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [hcoe n, hgae] with x hx hy
    simp [hx, ← hy]
  have hconv : Tendsto (fun n => dist (F n) G) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hG
  refine hconv.congr ?_
  intro n
  exact hdist2 n
