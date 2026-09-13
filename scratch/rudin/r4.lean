import Mathlib
open Filter Topology Set Real Polynomial

-- ch08_trigonometric_pi
example :
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

-- ch07_weierstrass_approximation
example (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ P : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n (x : ℝ) => (P n).eval (x : ℂ)) f atTop (Set.Icc a b) := by
  have hre : ContinuousOn (fun x => (f x).re) (Set.Icc a b) :=
    Complex.continuous_re.comp_continuousOn hf
  have him : ContinuousOn (fun x => (f x).im) (Set.Icc a b) :=
    Complex.continuous_im.comp_continuousOn hf
  have key : ∀ n : ℕ, ∃ P : Polynomial ℂ, ∀ x ∈ Set.Icc a b,
      ‖(P.eval (x : ℂ)) - f x‖ < 1 / (n + 1) := by
    intro n
    have hpos : (0:ℝ) < 1 / (2 * (n + 1)) := by positivity
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b _ hre _ hpos
    obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn a b _ him _ hpos
    refine ⟨p.map (algebraMap ℝ ℂ) + Complex.I • q.map (algebraMap ℝ ℂ), ?_⟩
    intro x hx
    have hpx := hp x hx
    have hqx := hq x hx
    set Pn : Polynomial ℂ := p.map (algebraMap ℝ ℂ) + Complex.I • q.map (algebraMap ℝ ℂ)
      with hPn
    have hev : Pn.eval (x : ℂ) = ((p.eval x : ℝ) : ℂ) + Complex.I * ((q.eval x : ℝ) : ℂ) := by
      have hax : ((x : ℝ) : ℂ) = algebraMap ℝ ℂ x := rfl
      rw [hPn]
      simp only [Polynomial.eval_add, Polynomial.eval_smul, Polynomial.eval_map, hax,
        Polynomial.eval₂_at_apply, smul_eq_mul]
      rfl
    have hrez : (Pn.eval (x : ℂ) - f x).re = p.eval x - (f x).re := by rw [hev]; simp
    have himz : (Pn.eval (x : ℂ) - f x).im = q.eval x - (f x).im := by rw [hev]; simp
    calc ‖Pn.eval (x : ℂ) - f x‖
        ≤ |(Pn.eval (x : ℂ) - f x).re| + |(Pn.eval (x : ℂ) - f x).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |p.eval x - (f x).re| + |q.eval x - (f x).im| := by rw [hrez, himz]
      _ < 1 / (2 * (n + 1)) + 1 / (2 * (n + 1)) := by linarith
      _ = 1 / (n + 1) := by
          have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
          field_simp
          ring
  choose P hP using key
  refine ⟨P, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  filter_upwards [eventually_ge_atTop N] with n hn x hx
  have h1 := hP n x hx
  have hNpos : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have : 1 / ((n:ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hNpos]
    have : (1:ℝ)/ε < (n:ℝ) + 1 := by
      calc (1:ℝ)/ε < N := hN
        _ ≤ (n:ℝ) := by exact_mod_cast hn
        _ < (n:ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hε] at this
    linarith
  rw [Complex.dist_eq]
  calc ‖f x - (P n).eval (x:ℂ)‖ = ‖(P n).eval (x:ℂ) - f x‖ := by rw [norm_sub_rev]
    _ < 1 / ((n:ℝ) + 1) := h1
    _ < ε := this
