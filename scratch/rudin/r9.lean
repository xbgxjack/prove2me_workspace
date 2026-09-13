import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

example (c : ℕ → ℝ) (C : ℝ) (hC : Rudin.SeriesConvergesTo c C) (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, |x| < 1 → Rudin.SeriesConvergesTo (fun n => c n * x ^ n) (f x)) :
    Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 C) := by
  -- the coefficients tend to 0
  have hc0 : Tendsto c atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => Rudin.partialSum c (n + 1)) atTop (𝓝 C) :=
      hC.comp (tendsto_add_atTop_nat 1)
    have h2 : ∀ n, c n = Rudin.partialSum c (n + 1) - Rudin.partialSum c n := by
      intro n
      simp [Rudin.partialSum, Finset.sum_range_succ]
    have h4 := h1.sub hC
    rw [sub_self] at h4
    have h3 : (fun n => Rudin.partialSum c (n + 1) - Rudin.partialSum c n) = c := by
      funext n; exact (h2 n).symm
    rwa [h3] at h4
  -- summability of the power series for |x| < 1
  have hsum : ∀ x : ℝ, |x| < 1 → Summable (fun n => c n * x ^ n) := by
    intro x hx
    have hgeo : Summable (fun n : ℕ => |x| ^ n) := summable_geometric_of_lt_one (abs_nonneg x) hx
    refine Summable.of_norm_bounded_eventually_nat hgeo ?_
    have hev : ∀ᶠ n in atTop, |c n| ≤ 1 := by
      have := hc0
      rw [Metric.tendsto_atTop] at this
      obtain ⟨N, hN⟩ := this 1 (by norm_num)
      filter_upwards [eventually_ge_atTop N] with n hn
      have := hN n hn
      rw [Real.dist_eq, sub_zero] at this
      linarith
    filter_upwards [hev] with n hn
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_of_le_one_left (by positivity) hn
  -- on (𝓝[<] 1) the function f agrees with the tsum
  have heq : ∀ᶠ x in 𝓝[<] (1 : ℝ), f x = ∑' n, c n * x ^ n := by
    have hmem : ∀ᶠ x in 𝓝[<] (1 : ℝ), (0 : ℝ) < x := by
      have : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) :=
        Ioo_mem_nhdsLT (by norm_num)
      filter_upwards [this] with x hx using hx.1
    have hlt : ∀ᶠ x in 𝓝[<] (1 : ℝ), x < 1 := eventually_mem_nhdsWithin.mono fun x hx => hx
    filter_upwards [hmem, hlt] with x hx0 hx1
    have hax : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
    have h1 := hf x hax
    have h2 : Tendsto (fun n => ∑ i ∈ Finset.range n, c i * x ^ i) atTop
        (𝓝 (∑' n, c n * x ^ n)) := (hsum x hax).hasSum.tendsto_sum_nat
    exact tendsto_nhds_unique h1 h2
  refine Tendsto.congr' (heq.mono fun x hx => hx.symm) ?_
  exact Real.tendsto_tsum_powerSeries_nhdsWithin_lt hC
