import Mathlib
open Filter Topology Set Real Polynomial

theorem solution :
    (∀ z w : ℂ, Complex.exp (z + w) = Complex.exp z * Complex.exp w) ∧
    (∀ x : ℝ, HasDerivAt Real.exp (Real.exp x) x) ∧
    StrictMono Real.exp ∧
    Tendsto Real.exp atTop atTop ∧
    Tendsto Real.exp atBot (𝓝 0) ∧
    (∀ n : ℕ, Tendsto (fun x : ℝ => x ^ n * Real.exp (-x)) atTop (𝓝 0)) :=
  ⟨fun z w => Complex.exp_add z w, Real.hasDerivAt_exp, Real.exp_strictMono,
    Real.tendsto_exp_atTop, Real.tendsto_exp_atBot,
    fun n => Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n⟩
