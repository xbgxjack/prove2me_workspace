import Mathlib
open Filter Topology Set Real

-- ch08_exp_properties
example :
    (∀ z w : ℂ, Complex.exp (z + w) = Complex.exp z * Complex.exp w) ∧
    (∀ x : ℝ, HasDerivAt Real.exp (Real.exp x) x) ∧
    StrictMono Real.exp ∧
    Tendsto Real.exp atTop atTop ∧
    Tendsto Real.exp atBot (𝓝 0) ∧
    (∀ n : ℕ, Tendsto (fun x : ℝ => x ^ n * Real.exp (-x)) atTop (𝓝 0)) :=
  ⟨fun z w => Complex.exp_add z w, Real.hasDerivAt_exp, Real.exp_strictMono,
    Real.tendsto_exp_atTop, Real.tendsto_exp_atBot,
    fun n => Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n⟩

-- ch08_gamma_functional_equation
example :
    (∀ x : ℝ, 0 < x → Real.Gamma (x + 1) = x * Real.Gamma x) ∧
    (∀ n : ℕ, Real.Gamma (n + 1) = n.factorial) ∧
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => Real.log (Real.Gamma x)) :=
  ⟨fun _ hx => Real.Gamma_add_one (ne_of_gt hx), Real.Gamma_nat_eq_factorial,
    Real.convexOn_log_Gamma⟩

-- ch05_darboux
example (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
    (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x) (A : ℝ)
    (hA : deriv f a < A ∧ A < deriv f b) :
    ∃ x ∈ Set.Ioo a b, deriv f x = A := by
  have hf : ∀ x ∈ Set.Icc a b, HasDerivWithinAt f (deriv f x) (Set.Icc a b) x :=
    fun x hx => (hfd x hx).hasDerivAt.hasDerivWithinAt
  obtain ⟨x, hx, hfx⟩ := exists_hasDerivWithinAt_eq_of_gt_of_lt hab.le hf hA.1 hA.2
  exact ⟨x, hx, hfx⟩

-- ch05_lhospital
example (a b : ℝ) (hab : a < b) (f g : ℝ → ℝ) (A : ℝ)
    (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
    (hgd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ g x)
    (hg' : ∀ x ∈ Set.Ioo a b, deriv g x ≠ 0)
    (hratio : Tendsto (fun x => deriv f x / deriv g x) (𝓝[>] a) (𝓝 A))
    (hf0 : Tendsto f (𝓝[>] a) (𝓝 0)) (hg0 : Tendsto g (𝓝[>] a) (𝓝 0)) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 A) :=
  deriv.lhopital_zero_right_on_Ioo hab (fun x hx => (hfd x hx).differentiableWithinAt) hg'
    hf0 hg0 hratio

-- ch09_bounded_derivative
example (n m : ℕ) (E : Set (EuclideanSpace ℝ (Fin n))) (hE : IsOpen E)
    (hconv : Convex ℝ E) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (f' : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hf : ∀ x ∈ E, HasFDerivAt f (f' x) x) (M : ℝ) (hM : ∀ x ∈ E, ‖f' x‖ ≤ M) :
    ∀ a ∈ E, ∀ b ∈ E, ‖f b - f a‖ ≤ M * ‖b - a‖ := by
  intro a ha b hb
  exact hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivWithinAt) hM ha hb
