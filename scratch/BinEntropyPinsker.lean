import Mathlib

open Real Set

/-- Pinsker-type quantitative bound for the binary entropy function: the entropy deficit
from `log 2` controls how far `p` is from `1/2`, quadratically. -/
theorem binEntropy_le_log_two_sub_sq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.binEntropy p ≤ Real.log 2 - 2 * (p - 1/2)^2 := by
  set g : ℝ → ℝ := fun p => Real.binEntropy p + 2 * (p - 1/2)^2 with hg_def
  have hgcont : ContinuousOn g (Icc 0 1) := by
    apply Continuous.continuousOn
    simp only [hg_def]
    fun_prop
  have hgdiff : DifferentiableOn ℝ g (interior (Icc (0:ℝ) 1)) := by
    rw [interior_Icc]
    intro p hp
    rw [mem_Ioo] at hp
    apply DifferentiableAt.differentiableWithinAt
    simp only [hg_def]
    apply DifferentiableAt.add
    · exact Real.differentiableAt_binEntropy hp.1.ne' hp.2.ne
    · fun_prop
  have hderiv_eq : ∀ p ∈ Ioo (0:ℝ) 1, deriv g p = Real.log (1-p) - Real.log p + 4*(p - 1/2) := by
    intro p hp
    rw [mem_Ioo] at hp
    have hbin : HasDerivAt Real.binEntropy (Real.log (1-p) - Real.log p) p :=
      Real.hasDerivAt_binEntropy hp.1.ne' hp.2.ne
    have hquad : HasDerivAt (fun p : ℝ => 2*(p-1/2)^2) (4*(p-1/2)) p := by
      have h1 : HasDerivAt (fun p : ℝ => p - 1/2) 1 p := (hasDerivAt_id p).sub_const _
      have h2 := (h1.fun_pow 2).const_mul (2:ℝ)
      norm_num at h2
      have hval : (4:ℝ) * (p - 1/2) = 2 * (2 * (p - 1/2)) := by ring
      rw [hval]
      exact h2
    have hg' : HasDerivAt g (Real.log (1-p) - Real.log p + 4*(p-1/2)) p := by
      rw [hg_def]; exact hbin.add hquad
    exact hg'.deriv
  have hgdiff' : DifferentiableOn ℝ (deriv g) (interior (Icc (0:ℝ) 1)) := by
    rw [interior_Icc]
    have hmodel : DifferentiableOn ℝ
        (fun p => Real.log (1-p) - Real.log p + 4*(p - 1/2)) (Ioo (0:ℝ) 1) := by
      intro p hp
      rw [mem_Ioo] at hp
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.add
      · apply DifferentiableAt.sub
        · fun_prop (disch := linarith)
        · fun_prop (disch := linarith)
      · fun_prop
    exact hmodel.congr (fun p hp => hderiv_eq p hp)
  have hderiv2_nonpos : ∀ p ∈ interior (Icc (0:ℝ) 1), deriv^[2] g p ≤ 0 := by
    rw [interior_Icc]
    intro p hp
    rw [mem_Ioo] at hp
    have heq2 : deriv^[2] g p = deriv (fun p => Real.log (1-p) - Real.log p + 4*(p - 1/2)) p := by
      rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply]
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [IsOpen.mem_nhds isOpen_Ioo hp] with x hx
      exact hderiv_eq x hx
    rw [heq2]
    have hd1 : HasDerivAt (fun p : ℝ => Real.log (1-p)) (-(1-p)⁻¹) p := by
      have h1 : HasDerivAt (fun p : ℝ => (1:ℝ) - p) (-1) p := by
        simpa using (hasDerivAt_id p).const_sub (1:ℝ)
      have h2 := h1.log (show (1:ℝ) - p ≠ 0 by linarith)
      convert h2 using 1
      field_simp
    have hd2 : HasDerivAt (fun p : ℝ => Real.log p) p⁻¹ p := Real.hasDerivAt_log hp.1.ne'
    have hd3 : HasDerivAt (fun p : ℝ => (4:ℝ)*(p - 1/2)) 4 p := by
      have h1 : HasDerivAt (fun p : ℝ => p - 1/2) 1 p := (hasDerivAt_id p).sub_const _
      simpa using h1.const_mul (4:ℝ)
    have hsum : HasDerivAt (fun p => Real.log (1-p) - Real.log p + 4*(p - 1/2))
        (-(1-p)⁻¹ - p⁻¹ + 4) p := (hd1.sub hd2).add hd3
    rw [hsum.deriv]
    have h14 : p * (1-p) ≤ 1/4 := by nlinarith [sq_nonneg (p - 1/2)]
    have hppos : 0 < p := hp.1
    have h1ppos : 0 < 1 - p := by linarith [hp.2]
    have hinv : 4 ≤ (1-p)⁻¹ + p⁻¹ := by
      rw [inv_add_inv h1ppos.ne' hppos.ne']
      rw [le_div_iff₀ (by positivity)]
      nlinarith [h14]
    linarith [hinv]
  have hconcave : ConcaveOn ℝ (Icc (0:ℝ) 1) g :=
    concaveOn_of_deriv2_nonpos (convex_Icc 0 1) hgcont hgdiff hgdiff' hderiv2_nonpos
  have hsymm : ∀ q ∈ Icc (0:ℝ) 1, g (1 - q) = g q := by
    intro q _
    simp only [hg_def]
    rw [Real.binEntropy_one_sub]
    ring_nf
  have hg_half : g (1/2) = Real.log 2 := by
    simp only [hg_def]
    rw [show (1:ℝ)/2 - 1/2 = 0 by ring]
    simp [Real.binEntropy_two_inv]
  have key : g p ≤ Real.log 2 := by
    rcases lt_trichotomy p (1/2) with hlt | heq | hgt
    · have hx : p ∈ Icc (0:ℝ) 1 := ⟨hp0, hp1⟩
      have hz : (1:ℝ) - p ∈ Icc (0:ℝ) 1 := by constructor <;> linarith
      have hyz : (1:ℝ)/2 < 1 - p := by linarith
      have hslope := hconcave.slope_anti_adjacent hx hz hlt hyz
      rw [hsymm p ⟨hp0, hp1⟩, show (1:ℝ) - p - 1/2 = 1/2 - p from by ring] at hslope
      have hpos : (0:ℝ) < 1/2 - p := by linarith
      rw [div_le_div_iff_of_pos_right hpos] at hslope
      rw [hg_half] at hslope
      linarith
    · rw [heq, hg_half]
    · have hx : (1:ℝ) - p ∈ Icc (0:ℝ) 1 := by constructor <;> linarith
      have hz : p ∈ Icc (0:ℝ) 1 := ⟨hp0, hp1⟩
      have hxy : (1:ℝ) - p < 1/2 := by linarith
      have hslope := hconcave.slope_anti_adjacent hx hz hxy hgt
      rw [hsymm p ⟨hp0, hp1⟩, show (1:ℝ)/2 - (1 - p) = p - 1/2 from by ring] at hslope
      have hpos : (0:ℝ) < p - 1/2 := by linarith
      rw [div_le_div_iff_of_pos_right hpos] at hslope
      rw [hg_half] at hslope
      linarith
  simp only [hg_def] at key
  linarith [key]
