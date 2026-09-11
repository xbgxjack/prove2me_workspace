import Definitions.Def_ReservoirESN
open ReservoirESN

private def picard {E S : Type*} [NormedAddCommGroup S] (F : S → E → S) (z : ℕ → E) :
    ℕ → ℕ → S
  | 0, _ => 0
  | n + 1, k => F (picard F z n (k + 1)) (z k)

private theorem picard_succ {E S : Type*} [NormedAddCommGroup S] (F : S → E → S) (z : ℕ → E)
    (n k : ℕ) : picard F z (n + 1) k = F (picard F z n (k + 1)) (z k) := rfl

private theorem picard_bdd {E S : Type*} [NormedAddCommGroup E] [NormedAddCommGroup S]
    (F : S → E → S) (L M r : ℝ) (hF : IsContracting F L M r) (z : ℕ → E) (hz : UnifBdd M z) :
    ∀ n k, ‖picard F z n k‖ ≤ L := by
  intro n
  induction n with
  | zero => intro k; show ‖(0 : S)‖ ≤ L; simpa using hF.state_radius_pos.le
  | succ n ih =>
    intro k
    rw [picard_succ]
    exact hF.maps_to _ _ (ih (k + 1)) (hz k)

private theorem picard_step_bound {E S : Type*} [NormedAddCommGroup E] [NormedAddCommGroup S]
    (F : S → E → S) (L M r : ℝ) (hF : IsContracting F L M r) (z : ℕ → E) (hz : UnifBdd M z) :
    ∀ n k, ‖picard F z (n + 1) k - picard F z n k‖ ≤ (2 * L) * r ^ n := by
  intro n
  induction n with
  | zero =>
    intro k
    have h0 : picard F z 0 k = (0 : S) := rfl
    rw [h0, sub_zero, pow_zero, mul_one]
    exact (picard_bdd F L M r hF z hz 1 k).trans (by linarith [hF.state_radius_pos])
  | succ n ih =>
    intro k
    rw [picard_succ, picard_succ]
    have hle := hF.contract (picard F z (n + 1) (k + 1)) (picard F z n (k + 1)) (z k)
      (picard_bdd F L M r hF z hz (n + 1) (k + 1))
      (picard_bdd F L M r hF z hz n (k + 1)) (hz k)
    calc ‖F (picard F z (n + 1) (k + 1)) (z k) - F (picard F z n (k + 1)) (z k)‖
        ≤ r * ‖picard F z (n + 1) (k + 1) - picard F z n (k + 1)‖ := hle
      _ ≤ r * ((2 * L) * r ^ n) := mul_le_mul_of_nonneg_left (ih (k + 1)) hF.nonneg
      _ = (2 * L) * r ^ (n + 1) := by ring

private theorem picard_cauchy {E S : Type*} [NormedAddCommGroup E] [NormedAddCommGroup S]
    (F : S → E → S) (L M r : ℝ) (hF : IsContracting F L M r) (z : ℕ → E) (hz : UnifBdd M z)
    (k : ℕ) : CauchySeq (fun n => picard F z n k) := by
  apply cauchySeq_of_le_geometric r (2 * L) hF.lt_one
  intro n
  rw [dist_eq_norm]
  have hstep := picard_step_bound F L M r hF z hz n k
  calc ‖picard F z n k - picard F z (n + 1) k‖
      = ‖picard F z (n + 1) k - picard F z n k‖ := norm_sub_rev _ _
    _ ≤ (2 * L) * r ^ n := hstep

theorem solution {E S : Type*} [NormedAddCommGroup E] [NormedAddCommGroup S]
    [CompleteSpace S] (F : S → E → S) (L M r : ℝ)
    (hF : IsContracting F L M r) (z : ℕ → E) (hz : UnifBdd M z) :
    ∃! x : ℕ → S, UnifBdd L x ∧ IsSolution F z x := by
  choose x hx using fun k => cauchySeq_tendsto_of_complete (picard_cauchy F L M r hF z hz k)
  have hbdd : UnifBdd L x := by
    intro k
    exact le_of_tendsto' (hx k).norm (fun n => picard_bdd F L M r hF z hz n k)
  have hsol : IsSolution F z x := by
    intro k
    have hn1 : Filter.Tendsto (fun n => picard F z (n + 1) k) Filter.atTop (nhds (x k)) :=
      (hx k).comp (Filter.tendsto_add_atTop_nat 1)
    have hdist0 : Filter.Tendsto (fun n => ‖picard F z n (k + 1) - x (k + 1)‖)
        Filter.atTop (nhds 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (hx (k + 1))
    have hzero : Filter.Tendsto
        (fun n => r * ‖picard F z n (k + 1) - x (k + 1)‖) Filter.atTop (nhds 0) := by
      have := hdist0.const_mul r
      simpa using this
    have hsqueeze : Filter.Tendsto
        (fun n => ‖F (picard F z n (k + 1)) (z k) - F (x (k + 1)) (z k)‖)
        Filter.atTop (nhds 0) := by
      apply squeeze_zero (fun n => norm_nonneg _) _ hzero
      intro n
      exact hF.contract (picard F z n (k + 1)) (x (k + 1)) (z k)
        (picard_bdd F L M r hF z hz n (k + 1)) (hbdd (k + 1)) (hz k)
    have hn2 : Filter.Tendsto (fun n => F (picard F z n (k + 1)) (z k)) Filter.atTop
        (nhds (F (x (k + 1)) (z k))) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr hsqueeze
    have heq : (fun n => picard F z (n + 1) k) = (fun n => F (picard F z n (k + 1)) (z k)) := by
      funext n; exact picard_succ F z n k
    rw [heq] at hn1
    exact tendsto_nhds_unique hn1 hn2
  refine ⟨x, ⟨hbdd, hsol⟩, ?_⟩
  rintro y ⟨hybdd, hysol⟩
  funext k
  have hyk : ∀ n, ‖y k - picard F z n k‖ ≤ (2 * L) * r ^ n := by
    intro n
    induction n generalizing k with
    | zero =>
      have h0 : picard F z 0 k = (0 : S) := rfl
      rw [h0, sub_zero, pow_zero, mul_one]
      exact (hybdd k).trans (by linarith [hF.state_radius_pos])
    | succ n ih =>
      rw [hysol k, picard_succ]
      have hle := hF.contract (y (k + 1)) (picard F z n (k + 1)) (z k)
        (hybdd (k + 1)) (picard_bdd F L M r hF z hz n (k + 1)) (hz k)
      calc ‖F (y (k + 1)) (z k) - F (picard F z n (k + 1)) (z k)‖
          ≤ r * ‖y (k + 1) - picard F z n (k + 1)‖ := hle
        _ ≤ r * ((2 * L) * r ^ n) := mul_le_mul_of_nonneg_left (ih (k + 1)) hF.nonneg
        _ = (2 * L) * r ^ (n + 1) := by ring
  have hrpow : Filter.Tendsto (fun n => (2 * L) * r ^ n) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hF.nonneg hF.lt_one).const_mul (2 * L)
    simpa using this
  have hto0 : Filter.Tendsto (fun n => ‖y k - picard F z n k‖) Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => norm_nonneg _) hyk hrpow
  have hlim : Filter.Tendsto (fun n => picard F z n k) Filter.atTop (nhds (y k)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have heq2 : (fun n => ‖picard F z n k - y k‖) = (fun n => ‖y k - picard F z n k‖) := by
      funext n; exact norm_sub_rev _ _
    rw [heq2]
    exact hto0
  exact (tendsto_nhds_unique (hx k) hlim).symm
