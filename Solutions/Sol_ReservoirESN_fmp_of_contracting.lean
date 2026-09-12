import Definitions.Def_ReservoirESN
open ReservoirESN

private theorem fmp_telescope {E S : Type*} [NormedAddCommGroup E] [NormedAddCommGroup S]
    (F : S → E → S) (L M r : ℝ) (hF : IsContracting F L M r)
    (z z' : ℕ → E) (x x' : ℕ → S)
    (hzM : UnifBdd M z) (hz'M : UnifBdd M z')
    (hxL : UnifBdd L x) (hx'L : UnifBdd L x')
    (hxsol : IsSolution F z x) (hx'sol : IsSolution F z' x') :
    ∀ n, ‖x 0 - x' 0‖ ≤ r ^ n * ‖x n - x' n‖ +
      ∑ j ∈ Finset.range n, r ^ j * ‖F (x (j + 1)) (z j) - F (x (j + 1)) (z' j)‖ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hr0 : 0 ≤ r := hF.nonneg
    have hxn : x n = F (x (n + 1)) (z n) := hxsol n
    have hx'n : x' n = F (x' (n + 1)) (z' n) := hx'sol n
    have hstep : ‖x n - x' n‖ ≤
        r * ‖x (n + 1) - x' (n + 1)‖ +
          ‖F (x (n + 1)) (z n) - F (x (n + 1)) (z' n)‖ := by
      rw [hxn, hx'n]
      have heq : F (x (n + 1)) (z n) - F (x' (n + 1)) (z' n) =
          (F (x (n + 1)) (z n) - F (x (n + 1)) (z' n)) +
            (F (x (n + 1)) (z' n) - F (x' (n + 1)) (z' n)) := by abel
      rw [heq]
      have htri := norm_add_le (F (x (n + 1)) (z n) - F (x (n + 1)) (z' n))
        (F (x (n + 1)) (z' n) - F (x' (n + 1)) (z' n))
      have hcontract := hF.contract (x (n + 1)) (x' (n + 1)) (z' n)
        (hxL (n + 1)) (hx'L (n + 1)) (hz'M n)
      linarith [htri, hcontract]
    have hmul := mul_le_mul_of_nonneg_left hstep (pow_nonneg hr0 n)
    have hsum_succ : ∑ j ∈ Finset.range (n + 1),
        r ^ j * ‖F (x (j + 1)) (z j) - F (x (j + 1)) (z' j)‖ =
        (∑ j ∈ Finset.range n, r ^ j * ‖F (x (j + 1)) (z j) - F (x (j + 1)) (z' j)‖) +
          r ^ n * ‖F (x (n + 1)) (z n) - F (x (n + 1)) (z' n)‖ :=
      Finset.sum_range_succ _ n
    rw [hsum_succ, pow_succ]
    nlinarith [ih, hmul]

theorem solution {E S : Type*} [NormedAddCommGroup E] [NormedAddCommGroup S]
    [CompleteSpace S] (F : S → E → S) (L M r : ℝ) (w : ℕ → ℝ)
    (hF : IsContracting F L M r) (hcont : UnifContInput F L M) (hw : IsWeighting w) :
    HasFadingMemory F L M w := by
  intro ε hε
  have hL := hF.state_radius_pos
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / (4 * L) by positivity) hF.lt_one
  set N := n + 1 with hNdef
  have hrN : r ^ N < ε / (4 * L) := by
    have hle1 : r ^ n * r ≤ r ^ n * 1 :=
      mul_le_mul_of_nonneg_left hF.lt_one.le (pow_nonneg hF.nonneg n)
    calc r ^ N = r ^ n * r := by rw [hNdef, pow_succ]
      _ ≤ r ^ n * 1 := hle1
      _ = r ^ n := by ring
      _ < ε / (4 * L) := hn
  have hNpos : 0 < N := Nat.succ_pos n
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hcont (ε / (2 * N)) (by positivity)
  have hwN1pos : 0 < w (N - 1) := hw.pos (N - 1)
  set δ := δ₀ * w (N - 1) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  refine ⟨δ, hδpos, ?_⟩
  intro z z' x x' hzM hz'M hxL hx'L hxsol hx'sol hwbdd
  have hcbound : ∀ j, j < N → ‖F (x (j + 1)) (z j) - F (x (j + 1)) (z' j)‖ < ε / (2 * N) := by
    intro j hj
    apply hδ₀ (x (j + 1)) (z j) (z' j) (hxL (j + 1)) (hzM j) (hz'M j)
    have hzz' : ‖z j - z' j‖ * w j ≤ δ := hwbdd j
    have hwjpos : 0 < w j := hw.pos j
    have hwj : w (N - 1) ≤ w j := hw.antitone (by omega)
    have hle : ‖z j - z' j‖ ≤ δ / w j := by
      rw [le_div_iff₀ hwjpos]; linarith [hzz']
    have hle2 : δ / w j ≤ δ / w (N - 1) :=
      div_le_div_of_nonneg_left hδpos.le hwN1pos hwj
    have heq3 : δ / w (N - 1) = δ₀ / 2 := by rw [hδdef]; field_simp
    calc ‖z j - z' j‖ ≤ δ / w j := hle
      _ ≤ δ / w (N - 1) := hle2
      _ = δ₀ / 2 := heq3
      _ < δ₀ := by linarith
  have htele := fmp_telescope F L M r hF z z' x x' hzM hz'M hxL hx'L hxsol hx'sol N
  have hsum_lt : ∑ j ∈ Finset.range N, r ^ j * ‖F (x (j + 1)) (z j) - F (x (j + 1)) (z' j)‖
      < ε / 2 := by
    have hrj1 : ∀ j, r ^ j ≤ 1 := fun j => pow_le_one₀ hF.nonneg hF.lt_one.le
    have hstep1 : ∑ j ∈ Finset.range N, r ^ j * ‖F (x (j + 1)) (z j) - F (x (j + 1)) (z' j)‖
        ≤ ∑ j ∈ Finset.range N, ‖F (x (j + 1)) (z j) - F (x (j + 1)) (z' j)‖ := by
      apply Finset.sum_le_sum
      intro j _
      calc r ^ j * ‖F (x (j + 1)) (z j) - F (x (j + 1)) (z' j)‖
          ≤ 1 * ‖F (x (j + 1)) (z j) - F (x (j + 1)) (z' j)‖ :=
            mul_le_mul_of_nonneg_right (hrj1 j) (norm_nonneg _)
        _ = ‖F (x (j + 1)) (z j) - F (x (j + 1)) (z' j)‖ := by ring
    have hstep2 : ∑ j ∈ Finset.range N, ‖F (x (j + 1)) (z j) - F (x (j + 1)) (z' j)‖
        < ∑ _j ∈ Finset.range N, ε / (2 * N) := by
      apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hNpos.ne')
      intro j hj
      exact hcbound j (Finset.mem_range.mp hj)
    have hstep3 : (∑ _j ∈ Finset.range N, ε / (2 * N)) = ε / 2 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    linarith [hstep1, hstep2, hstep3.le, hstep3.ge]
  have he_N : ‖x N - x' N‖ ≤ 2 * L := by
    calc ‖x N - x' N‖ ≤ ‖x N‖ + ‖x' N‖ := norm_sub_le _ _
      _ ≤ L + L := add_le_add (hxL N) (hx'L N)
      _ = 2 * L := by ring
  have hrNe : r ^ N * ‖x N - x' N‖ < ε / 2 := by
    have hs1 : r ^ N * ‖x N - x' N‖ ≤ r ^ N * (2 * L) :=
      mul_le_mul_of_nonneg_left he_N (pow_nonneg hF.nonneg N)
    have hs2 : r ^ N * (2 * L) < (ε / (4 * L)) * (2 * L) :=
      mul_lt_mul_of_pos_right hrN (by linarith)
    have hs3 : (ε / (4 * L)) * (2 * L) = ε / 2 := by field_simp; ring
    linarith [hs1, hs2, hs3.le, hs3.ge]
  linarith [htele, hsum_lt, hrNe]
