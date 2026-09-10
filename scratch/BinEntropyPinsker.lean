import Mathlib

open Real Set

/-- Pinsker-type quantitative bound for the binary entropy function: the entropy deficit
from `log 2` controls how far `p` is from `1/2`, quadratically. -/
theorem binEntropy_le_log_two_sub_sq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.binEntropy p ≤ Real.log 2 - 2 * (p - 1/2)^2 := by
  set g : ℝ → ℝ := fun p => Real.binEntropy p + 2 * (p - 1/2)^2 with hg_def
  have hgcont : ContinuousOn g (Icc 0 1) := by
    apply Continuous.continuousOn
    unfold_let g
    fun_prop
  have hgdiff : DifferentiableOn ℝ g (interior (Icc (0:ℝ) 1)) := by
    rw [interior_Icc]
    intro p hp
    rw [mem_Ioo] at hp
    apply DifferentiableAt.differentiableWithinAt
    unfold_let g
    apply DifferentiableAt.add
    · exact Real.differentiableAt_binEntropy hp.1.ne' hp.2.ne
    · fun_prop
  have hderiv_eq : ∀ p ∈ Ioo (0:ℝ) 1, deriv g p = Real.log (1-p) - Real.log p + 4*(p - 1/2) := by
    intro p hp
    rw [mem_Ioo] at hp
    unfold_let g
    rw [deriv_add (Real.differentiableAt_binEntropy hp.1.ne' hp.2.ne) (by fun_prop),
      Real.deriv_binEntropy]
    congr 1
    rw [show (fun p => 2*(p-1/2)^2) = (fun p => 2*(p-1/2)^2) from rfl]
    rw [show deriv (fun p : ℝ => 2*(p-1/2)^2) p = 4*(p-1/2) from by
      have : HasDerivAt (fun p : ℝ => 2*(p-1/2)^2) (4*(p-1/2)) p := by
        have h1 : HasDerivAt (fun p : ℝ => p - 1/2) 1 p := (hasDerivAt_id p).sub_const _
        have h2 := h1.pow 2
        simp only [Nat.cast_ofNat, Nat.succ_sub_succ_eq_sub, tsub_zero, pow_one, mul_one] at h2
        have h3 := h2.const_mul 2
        convert h3 using 1
        ring
      exact this.deriv]
  have hgdiff' : DifferentiableOn ℝ (deriv g) (interior (Icc (0:ℝ) 1)) := by
    rw [interior_Icc]
    apply DifferentiableOn.congr (f := fun p => Real.log (1-p) - Real.log p + 4*(p - 1/2))
    · fun_prop (disch := intros; simp_all; intro hh; nlinarith [Set.mem_Ioo.mp (by assumption : _ ∈ Ioo (0:ℝ) 1)])
    · intro p hp
      exact (hderiv_eq p hp).symm
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
      have h2 := (Real.hasDerivAt_log (by linarith : (1:ℝ) - p ≠ 0)).comp p h1
      simpa using h2
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
      rw [ge_iff_le, le_div_iff₀ (by positivity)]
      nlinarith [h14]
    linarith [hinv]
  have hconcave : ConcaveOn ℝ (Icc (0:ℝ) 1) g :=
    concaveOn_of_deriv2_nonpos (convex_Icc 0 1) hgcont hgdiff hgdiff' hderiv2_nonpos
  have hsymm : ∀ q ∈ Icc (0:ℝ) 1, g (1 - q) = g q := by
    intro q _
    unfold_let g
    rw [Real.binEntropy_one_sub]
    ring_nf
  have hg_half : g (1/2) = Real.log 2 := by
    unfold_let g
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
      rw [div_le_div_iff_right hpos] at hslope
      rw [hg_half] at hslope ⊢
      linarith
    · rw [heq, hg_half]
    · have hx : (1:ℝ) - p ∈ Icc (0:ℝ) 1 := by constructor <;> linarith
      have hz : p ∈ Icc (0:ℝ) 1 := ⟨hp0, hp1⟩
      have hxy : (1:ℝ) - p < 1/2 := by linarith
      have hslope := hconcave.slope_anti_adjacent hx hz hxy hgt
      rw [hsymm p ⟨hp0, hp1⟩, show (1:ℝ)/2 - (1 - p) = p - 1/2 from by ring] at hslope
      have hpos : (0:ℝ) < p - 1/2 := by linarith
      rw [div_le_div_iff_right hpos] at hslope
      rw [hg_half] at hslope ⊢
      linarith
  unfold_let g at key
  linarith [key]
