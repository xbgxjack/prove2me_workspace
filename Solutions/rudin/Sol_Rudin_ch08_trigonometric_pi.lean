import Mathlib
open Filter Topology Set Real Polynomial

theorem solution :
    Real.cos (Real.pi / 2) = 0 ∧
    (∀ x ∈ Set.Ico (0 : ℝ) (Real.pi / 2), 0 < Real.cos x) ∧
    (∀ z : ℂ, Complex.exp (z + 2 * Real.pi * Complex.I) = Complex.exp z) ∧
    (∀ z : ℂ, ‖z‖ = 1 → ∃ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
      z = Complex.exp (t * Complex.I)) := by
  refine ⟨Real.cos_pi_div_two, ?_, ?_, ?_⟩
  · intro x hx
    refine Real.cos_pos_of_mem_Ioo ⟨?_, hx.2⟩
    have : (0:ℝ) < Real.pi := Real.pi_pos
    linarith [hx.1]
  · intro z
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  · intro z hz
    have hzarg : (‖z‖ : ℂ) * Complex.exp (Complex.arg z * Complex.I) = z :=
      Complex.norm_mul_exp_arg_mul_I z
    rw [hz] at hzarg
    push_cast at hzarg
    rw [one_mul] at hzarg
    rcases le_or_gt 0 (Complex.arg z) with h | h
    · refine ⟨Complex.arg z, ⟨h, ?_⟩, hzarg.symm⟩
      have := Complex.arg_le_pi z
      have hp := Real.pi_pos
      linarith
    · refine ⟨Complex.arg z + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
      · have := Complex.neg_pi_lt_arg z
        have hp := Real.pi_pos
        linarith
      · linarith
      · symm
        have hc : ((Complex.arg z + 2 * Real.pi : ℝ) : ℂ) * Complex.I
            = (Complex.arg z : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by
          push_cast; ring
        rw [hc, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
        exact hzarg
