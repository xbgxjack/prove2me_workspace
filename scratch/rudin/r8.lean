import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory

example {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ)
    (hf : Rudin.MemL2 μ f) (hg : Rudin.MemL2 μ g) :
    Integrable (fun x => f x * g x) μ ∧
      |∫ x, f x * g x ∂μ| ≤ Rudin.L2Norm μ f * Rudin.L2Norm μ g := by
  obtain ⟨hfm, hfi⟩ := hf
  obtain ⟨hgm, hgi⟩ := hg
  -- integrability of the product
  have hbound : Integrable (fun x => (f x ^ 2 + g x ^ 2) / 2) μ := by
    exact (hfi.add hgi).div_const 2
  have hfg : Integrable (fun x => f x * g x) μ := by
    refine Integrable.mono' hbound ((hfm.mul hgm).aestronglyMeasurable) ?_
    filter_upwards with x
    have h := sq_nonneg (|f x| - |g x|)
    have habs : ‖f x * g x‖ = |f x| * |g x| := by
      rw [Real.norm_eq_abs, abs_mul]
    rw [habs]
    nlinarith [sq_abs (f x), sq_abs (g x)]
  set A := ∫ x, f x ^ 2 ∂μ with hA
  set B := ∫ x, f x * g x ∂μ with hB
  set C := ∫ x, g x ^ 2 ∂μ with hC
  have hA0 : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  have hC0 : 0 ≤ C := integral_nonneg fun x => sq_nonneg _
  have hquad : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * C := by
    intro t
    have hi2 : Integrable (fun x => 2 * t * (f x * g x) + t ^ 2 * g x ^ 2) μ :=
      (hfg.const_mul (2 * t)).add (hgi.const_mul (t ^ 2))
    have e1 : ∫ x, (f x ^ 2 + (2 * t * (f x * g x) + t ^ 2 * g x ^ 2)) ∂μ
        = (∫ x, f x ^ 2 ∂μ) + ∫ x, (2 * t * (f x * g x) + t ^ 2 * g x ^ 2) ∂μ :=
      integral_add hfi hi2
    have e2 : ∫ x, (2 * t * (f x * g x) + t ^ 2 * g x ^ 2) ∂μ
        = (∫ x, 2 * t * (f x * g x) ∂μ) + ∫ x, t ^ 2 * g x ^ 2 ∂μ :=
      integral_add (hfg.const_mul (2 * t)) (hgi.const_mul (t ^ 2))
    have e3 : ∫ x, 2 * t * (f x * g x) ∂μ = 2 * t * B := by
      rw [integral_const_mul, hB]
    have e4 : ∫ x, t ^ 2 * g x ^ 2 ∂μ = t ^ 2 * C := by
      rw [integral_const_mul, hC]
    have hnn : 0 ≤ ∫ x, (f x + t * g x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have hre : (fun x => (f x + t * g x) ^ 2)
        = fun x => f x ^ 2 + (2 * t * (f x * g x) + t ^ 2 * g x ^ 2) := by
      funext x; ring
    rw [hre, e1, e2, e3, e4, ← hA] at hnn
    linarith
  have hAC : B ^ 2 ≤ A * C := by
    rcases eq_or_lt_of_le hC0 with hCz | hCp
    · have hB0 : B = 0 := by
        by_contra hBne
        have h := hquad (-(A + 1) / (2 * B))
        rw [← hCz] at h
        have hcalc : A + 2 * (-(A + 1) / (2 * B)) * B + (-(A + 1) / (2 * B)) ^ 2 * 0 = -1 := by
          field_simp
          ring
        rw [hcalc] at h
        linarith
      rw [hB0]; nlinarith
    · have h := hquad (-B / C)
      have hCne : C ≠ 0 := ne_of_gt hCp
      have key : (A + 2 * (-B / C) * B + (-B / C) ^ 2 * C) * C = A * C - B ^ 2 := by
        field_simp; ring
      have hmul := mul_nonneg h hC0
      rw [key] at hmul
      linarith
  refine ⟨hfg, ?_⟩
  have h1 : |B| = Real.sqrt (B ^ 2) := (Real.sqrt_sq_eq_abs B).symm
  rw [Rudin.L2Norm, Rudin.L2Norm, ← hA, ← hC, h1, ← Real.sqrt_mul hA0]
  exact Real.sqrt_le_sqrt hAC
