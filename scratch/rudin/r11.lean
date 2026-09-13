import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

set_option maxHeartbeats 1000000

private lemma bdd_of_tendsto_zero {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0)) :
    ∃ M : ℝ, 0 < M ∧ ∀ n, |u n| ≤ M := by
  rw [Metric.tendsto_atTop] at hu
  obtain ⟨N, hN⟩ := hu 1 one_pos
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  refine ⟨max 1 ((Finset.range (N + 1)).sup' hne (fun n => |u n|)),
    lt_of_lt_of_le one_pos (le_max_left _ _), fun n => ?_⟩
  rcases Nat.lt_or_ge n N with h | h
  · refine le_trans ?_ (le_max_right _ _)
    exact Finset.le_sup' (fun n => |u n|) (Finset.mem_range.mpr (by omega))
  · have := hN n h
    rw [Real.dist_eq, sub_zero] at this
    exact le_trans this.le (le_max_left _ _)

/-- Coefficients of a convergent power series are dominated by a geometric sequence. -/
private lemma coeff_bound {c : ℕ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : Rudin.SeriesConverges (fun n => c n * ρ ^ n)) :
    ∃ M : ℝ, 0 < M ∧ ∀ n, |c n| * ρ ^ n ≤ M := by
  obtain ⟨s, hs⟩ := h
  have hterm : Tendsto (fun n => c n * ρ ^ n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => Rudin.partialSum (fun n => c n * ρ ^ n) (n + 1)) atTop (𝓝 s) :=
      hs.comp (tendsto_add_atTop_nat 1)
    have h2 : ∀ n, c n * ρ ^ n = Rudin.partialSum (fun n => c n * ρ ^ n) (n + 1)
        - Rudin.partialSum (fun n => c n * ρ ^ n) n := by
      intro n; simp [Rudin.partialSum, Finset.sum_range_succ]
    have h4 := h1.sub hs
    rw [sub_self] at h4
    have h3 : (fun n => Rudin.partialSum (fun n => c n * ρ ^ n) (n + 1)
        - Rudin.partialSum (fun n => c n * ρ ^ n) n) = fun n => c n * ρ ^ n := by
      funext n; exact (h2 n).symm
    rwa [h3] at h4
  obtain ⟨M, hM0, hM⟩ := bdd_of_tendsto_zero hterm
  refine ⟨M, hM0, fun n => ?_⟩
  have := hM n
  rwa [abs_mul, abs_of_pos (pow_pos hρ n)] at this

example (c : ℕ → ℝ) (R : ℝ) (hR : 0 < R)
    (hconv : ∀ x : ℝ, |x| < R → Rudin.SeriesConverges (fun n => c n * x ^ n))
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, |x| < R → Rudin.SeriesConvergesTo (fun n => c n * x ^ n) (f x))
    (g : ℝ → ℝ) (hg : ∀ x : ℝ, |x| < R →
      Rudin.SeriesConvergesTo (fun n => (n : ℝ) * c n * x ^ (n - 1)) (g x)) :
    ∀ x : ℝ, |x| < R → HasDerivAt f (g x) x := by
  intro x hx
  obtain ⟨r, hr0, hxr, hrR⟩ : ∃ r : ℝ, 0 < r ∧ |x| < r ∧ r < R :=
    ⟨(|x| + R) / 2, by linarith [abs_nonneg x], by linarith, by linarith [abs_nonneg x]⟩
  obtain ⟨ρ, hρ0, hrρ, hρR⟩ : ∃ ρ : ℝ, 0 < ρ ∧ r < ρ ∧ ρ < R :=
    ⟨(r + R) / 2, by linarith, by linarith, by linarith⟩
  obtain ⟨M, hM0, hM⟩ := coeff_bound hρ0 (hconv ρ (by rw [abs_of_pos hρ0]; exact hρR))
  have hq0 : (0:ℝ) ≤ r / ρ := by positivity
  have hq' : r / ρ < 1 := by rw [div_lt_one hρ0]; exact hrρ
  have hq : |r / ρ| < 1 := by rwa [abs_of_nonneg hq0]
  -- summable majorants
  have hU : Summable (fun n : ℕ => M / r * (n : ℝ) * (r / ρ) ^ n) := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (by simpa using hq)
    simpa [pow_one, mul_assoc] using this.mul_left (M / r)
  have hV : Summable (fun n : ℕ => M * (r / ρ) ^ n) :=
    (summable_geometric_of_lt_one hq0 hq').mul_left M
  -- pointwise bounds
  have hcoef : ∀ n : ℕ, |c n| ≤ M / ρ ^ n := fun n => by
    rw [le_div_iff₀ (pow_pos hρ0 n)]; exact hM n
  have hboundV : ∀ (n : ℕ) (y : ℝ), |y| ≤ r → ‖c n * y ^ n‖ ≤ M * (r / ρ) ^ n := by
    intro n y hy
    have h1 : |y| ^ n ≤ r ^ n := pow_le_pow_left₀ (abs_nonneg y) hy n
    calc ‖c n * y ^ n‖ = |c n| * |y| ^ n := by rw [Real.norm_eq_abs, abs_mul, abs_pow]
      _ ≤ (M / ρ ^ n) * r ^ n :=
        mul_le_mul (hcoef n) h1 (by positivity) (by positivity)
      _ = M * (r / ρ) ^ n := by rw [div_pow]; field_simp
  have hboundU : ∀ (n : ℕ) (y : ℝ), |y| ≤ r →
      ‖(n : ℝ) * c n * y ^ (n - 1)‖ ≤ M / r * (n : ℝ) * (r / ρ) ^ n := by
    intro n y hy
    match n with
    | 0 => simp
    | (m + 1) =>
      simp only [Nat.add_sub_cancel]
      have h1 : |y| ^ m ≤ r ^ m := pow_le_pow_left₀ (abs_nonneg y) hy m
      have hcm : |c (m + 1)| ≤ M / ρ ^ (m + 1) := hcoef (m + 1)
      have hmn : (0:ℝ) ≤ (m : ℝ) + 1 := by positivity
      calc ‖((m + 1 : ℕ) : ℝ) * c (m + 1) * y ^ m‖
          = ((m : ℝ) + 1) * (|c (m + 1)| * |y| ^ m) := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
            push_cast
            rw [abs_of_nonneg hmn, mul_assoc]
        _ ≤ ((m : ℝ) + 1) * ((M / ρ ^ (m + 1)) * r ^ m) := by
            refine mul_le_mul_of_nonneg_left ?_ hmn
            exact mul_le_mul hcm h1 (by positivity) (by positivity)
        _ = M / r * ((m + 1 : ℕ) : ℝ) * (r / ρ) ^ (m + 1) := by
            rw [div_pow]; push_cast; field_simp; ring
  -- the derivative of the tsum
  have ht : IsOpen (Set.Ioo (-r) r) := isOpen_Ioo
  have htp : IsPreconnected (Set.Ioo (-r) r) := (convex_Ioo (-r) r).isPreconnected
  have hxt : x ∈ Set.Ioo (-r) r := by
    rw [Set.mem_Ioo]; constructor <;> [linarith [neg_abs_le x]; linarith [le_abs_self x]]
  have h0t : (0:ℝ) ∈ Set.Ioo (-r) r := by rw [Set.mem_Ioo]; constructor <;> linarith
  have hyle : ∀ y ∈ Set.Ioo (-r) r, |y| ≤ r := by
    intro y hy
    rw [abs_le]
    exact ⟨hy.1.le, hy.2.le⟩
  have hderiv : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r →
      HasDerivAt (fun z : ℝ => c n * z ^ n) ((n : ℝ) * c n * y ^ (n - 1)) y := by
    intro n y _
    have h := (hasDerivAt_pow n y).const_mul (c n)
    have he : c n * ((n : ℝ) * y ^ (n - 1)) = (n : ℝ) * c n * y ^ (n - 1) := by ring
    rwa [he] at h
  have hg0 : Summable (fun n => c n * (0:ℝ) ^ n) :=
    Summable.of_norm_bounded hV (fun n => hboundV n 0 (by simpa using hr0.le))
  have hmain := hasDerivAt_tsum_of_isPreconnected hU ht htp hderiv
    (fun n y hy => hboundU n y (hyle y hy)) h0t hg0 hxt
  -- identify the tsums with f and g
  have hfeq : ∀ y ∈ Set.Ioo (-r) r, (∑' n, c n * y ^ n) = f y := by
    intro y hy
    have hyR : |y| < R := lt_of_le_of_lt (hyle y hy) hrR
    have hsum : Summable (fun n => c n * y ^ n) :=
      Summable.of_norm_bounded hV (fun n => hboundV n y (hyle y hy))
    exact tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat (hf y hyR)
  have hgeq : (∑' n : ℕ, (n : ℝ) * c n * x ^ (n - 1)) = g x := by
    have hsum : Summable (fun n : ℕ => (n : ℝ) * c n * x ^ (n - 1)) :=
      Summable.of_norm_bounded hU (fun n => hboundU n x (hyle x hxt))
    exact tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat (hg x hx)
  rw [hgeq] at hmain
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [ht.mem_nhds hxt] with y hy
  exact (hfeq y hy).symm
