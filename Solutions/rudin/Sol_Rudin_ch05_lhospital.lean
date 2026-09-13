import Mathlib
open Filter Topology Set Real Polynomial

theorem solution (a b : ℝ) (hab : a < b) (f g : ℝ → ℝ) (A : ℝ)
    (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
    (hgd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ g x)
    (hg' : ∀ x ∈ Set.Ioo a b, deriv g x ≠ 0)
    (hratio : Tendsto (fun x => deriv f x / deriv g x) (𝓝[>] a) (𝓝 A))
    (hf0 : Tendsto f (𝓝[>] a) (𝓝 0)) (hg0 : Tendsto g (𝓝[>] a) (𝓝 0)) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 A) :=
  deriv.lhopital_zero_right_on_Ioo hab (fun x hx => (hfd x hx).differentiableWithinAt) hg'
    hf0 hg0 hratio
