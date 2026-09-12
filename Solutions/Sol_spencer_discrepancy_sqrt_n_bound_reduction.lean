import Mathlib
import Definitions.Def_RSign
import Theorems.Thm_lemma8_partial_coloring_round

open Finset

/-! This solution reduces to `lemma8_partial_coloring_round` (Rothvoß's
Lemma 8, imported here — itself a reduction to the still-Open Lemma 9,
`shannonEntropy_shellFin_le`), and otherwise assembles the outer geometric
iteration: a numeric telescoping-sum bound for repeatedly applying Lemma 8
on a shrinking active column set, and a strong induction (tracking the
active set as a shrinking `Finset (Fin n)`) that combines the rounds into
a full coloring of all `n` columns. -/

/-- `Real.negMulLog` is strictly increasing on `[0, 1/e]`, used by
`iterX_mono` below to show the per-round bound is monotone in the active
size. -/
lemma negMulLog_strictMonoOn : StrictMonoOn Real.negMulLog (Set.Icc 0 (Real.exp (-1))) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) Real.continuous_negMulLog.continuousOn
  intro x hx
  rw [interior_Icc, Set.mem_Ioo] at hx
  obtain ⟨hx0, hx1⟩ := hx
  rw [Real.deriv_negMulLog (ne_of_gt hx0)]
  have hlogx : Real.log x < -1 := by
    have := Real.log_lt_log hx0 hx1
    rwa [Real.log_exp] at this
  linarith

/-! ## The outer geometric iteration: telescoping-sum bound

`lemma8_partial_coloring_round` gives ONE round's contribution
`λ(m)·√m` where `λ(m)` is chosen fresh from whatever the ACTUAL active
size `m` happens to be at that round (never from a pre-committed
round-index guess — the active size can shrink faster than the
guaranteed 10% per round, and a λ sized for an over-estimate of `m`
would be too small for the real, smaller `m`). Iterating from `m₀ = n`
down through active sizes `m₀ ≥ m₁ ≥ m₂ ≥ …`, each satisfying
`m_{k+1} ≤ 0.9·m_k` (guaranteed by Lemma 8, regardless of how much
extra got colored), the total row bound is `Σ_k λ(m_k)·√(m_k)`.

Since `λ(m)·√m` is monotone increasing in `m` (checked: for `m ≤ n`,
`m·ln(C/m)` is increasing whenever `m < C/e`, which holds throughout
since `C := 120n/log2 ≈ 173n ≫ n·e`), and `m_k ≤ n·0.9^k` (a genuine
upper bound, provable by a simple induction, unaffected by rounds
over-performing), we get `λ(m_k)·√(m_k) ≤ λ(n·0.9^k)·√(n·0.9^k)`
termwise — so the (variable-length, run-dependent) actual sum is
bounded by the sum of this explicit, IDEALIZED round-indexed sequence,
for ANY number of terms. That idealized sum is what's bounded below:
it decays geometrically (`0.9^{k/2}`) despite `λ` growing like
`√(log(1/0.9^k))` — a genuinely converging series, bounded here via
comparison to a arithmetic-geometric series `Σ(k+1)r^k`, which has a
clean closed form. -/

noncomputable section

/-- The λ that makes `lemma8_partial_coloring_round`'s entropy budget
`n·(12/log2)·exp(-λ²/4) ≤ m/10` hold with EQUALITY at active size `m`
(for fixed total row count `n`). -/
def iterLam (n m : ℝ) : ℝ := 2 * Real.sqrt (Real.log (120*n/(m*Real.log 2)))

/-- The per-round row-bound contribution `λ(m)·√m`. -/
def iterX (n m : ℝ) : ℝ := iterLam n m * Real.sqrt m

/-- `iterLam` exactly saturates the entropy budget: plugging it into
`lemma8_partial_coloring_round`'s hypothesis gives equality, hence `≤`. -/
lemma iterLam_budget_eq (n m : ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) :
    n * ((12/Real.log 2) * Real.exp (-(iterLam n m)^2/4)) = m/10 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hCpos : 0 < 120*n/(m*Real.log 2) := by positivity
  unfold iterLam
  rw [show (2 * Real.sqrt (Real.log (120*n/(m*Real.log 2))))^2
      = 4 * Real.log (120*n/(m*Real.log 2)) by
        rw [mul_pow, Real.sq_sqrt (Real.log_nonneg ?_)]
        · ring
        · rw [le_div_iff₀ (by positivity : (0:ℝ) < m*Real.log 2)]
          nlinarith [hn, hm, hmn, hlog2pos, hlog2lt1,
            mul_le_mul_of_nonneg_left hlog2lt1.le hm.le]]
  rw [show -(4 * Real.log (120*n/(m*Real.log 2)))/4 = -Real.log (120*n/(m*Real.log 2)) by ring,
    Real.exp_neg, Real.exp_log hCpos]
  field_simp
  ring

/-- `Real.sqrt` commutes with natural powers, for a nonneg base. -/
lemma real_sqrt_pow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : Real.sqrt (x^k) = (Real.sqrt x)^k := by
  induction k with
  | zero => simp
  | succ j ih => rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hx j), ih]

/-- Closed form for `Σ_{k=0}^{N-1} (k+1)·r^k`, needed to bound the
polynomial-times-geometric series arising from `λ`'s slow logarithmic
growth against the geometric shrinkage of the active set. -/
lemma arith_geom_partial_sum_eq (r : ℝ) (hr1 : r ≠ 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k:ℝ)+1) * r^k
      = (1 - r^N)/(1-r)^2 - (N:ℝ)*r^N/(1-r) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1mr : (1:ℝ) - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
    push_cast
    field_simp
    ring

lemma arith_geom_partial_sum_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k:ℝ)+1) * r^k ≤ 1/(1-r)^2 := by
  rw [arith_geom_partial_sum_eq r (ne_of_lt hr1) N]
  have h1mr : 0 < 1 - r := by linarith
  have h1 : (1-r^N)/(1-r)^2 ≤ 1/(1-r)^2 :=
    div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 N]) (by positivity)
  have h2 : 0 ≤ (N:ℝ)*r^N/(1-r) := by positivity
  linarith [h1, h2]

/-- The idealized (round-indexed) telescoping-sum bound: no matter how
many rounds `N` are used, `Σ_{k<N} iterX n (n·(9/10)^k) ≤ [explicit
constant]·√n`. The geometric decay `(√(9/10))^k` beats the logarithmic
growth of `iterLam`, so the series converges to an absolute
(n-independent) multiple of `√n`. -/
lemma iterX_sum_le (n : ℝ) (hn : 0 < n) (N : ℕ) :
    ∑ k ∈ Finset.range N, iterX n (n * (9/10)^k)
      ≤ 2 * Real.sqrt (Real.log (120/Real.log 2) + Real.log (10/9))
          * (1 / (1 - Real.sqrt (9/10)))^2 * Real.sqrt n := by
  set A : ℝ := Real.log (120/Real.log 2) with hAdef
  set B : ℝ := Real.log (10/9) with hBdef
  set ρ : ℝ := Real.sqrt (9/10) with hρdef
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hne_log2 : Real.log 2 ≠ 0 := hlog2pos.ne'
  have hne_n : (n:ℝ) ≠ 0 := ne_of_gt hn
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ < 1 := by
    rw [hρdef, show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hApos : 0 < A := by
    rw [hAdef]; apply Real.log_pos; rw [lt_div_iff₀ hlog2pos]; nlinarith [Real.log_two_lt_d9]
  have hBpos : 0 < B := Real.log_pos (by norm_num)
  have hterm : ∀ k ∈ Finset.range N,
      iterX n (n * (9/10)^k) ≤ 2*Real.sqrt (A+B) * ((k:ℝ)+1) * ρ^k * Real.sqrt n := by
    intro k _
    have hne_p : ((9:ℝ)/10)^k ≠ 0 := by positivity
    have heq1 : iterLam n (n * (9/10)^k) = 2 * Real.sqrt (A + (k:ℝ)*B) := by
      unfold iterLam
      congr 2
      have hkey : (120:ℝ)*n/(n*(9/10)^k*Real.log 2) = (120/Real.log 2) * (10/9)^k := by
        rw [show (10:ℝ)/9 = ((9:ℝ)/10)⁻¹ by norm_num, inv_pow]
        field_simp
      rw [hkey, Real.log_mul (by positivity) (by positivity), Real.log_pow, hAdef, hBdef]
    have heq2 : Real.sqrt (n * (9/10)^k) = Real.sqrt n * ρ^k := by
      rw [Real.sqrt_mul hn.le, hρdef, real_sqrt_pow (9/10) (by norm_num) k]
    have hle : Real.sqrt (A + (k:ℝ)*B) ≤ Real.sqrt (A+B) * ((k:ℝ)+1) := by
      have hsq : (A + (k:ℝ)*B) ≤ (A+B)*((k:ℝ)+1)^2 := by
        nlinarith [sq_nonneg ((k:ℝ)), hApos.le, hBpos.le, (Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ))]
      calc Real.sqrt (A + (k:ℝ)*B) ≤ Real.sqrt ((A+B)*((k:ℝ)+1)^2) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (A+B) * ((k:ℝ)+1) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    unfold iterX
    rw [heq1, heq2]
    calc 2 * Real.sqrt (A + (k:ℝ)*B) * (Real.sqrt n * ρ^k)
        ≤ 2 * (Real.sqrt (A+B) * ((k:ℝ)+1)) * (Real.sqrt n * ρ^k) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left hle (by norm_num)
      _ = 2*Real.sqrt (A+B) * ((k:ℝ)+1) * ρ^k * Real.sqrt n := by ring
  calc ∑ k ∈ Finset.range N, iterX n (n * (9/10)^k)
      ≤ ∑ k ∈ Finset.range N, 2*Real.sqrt (A+B) * ((k:ℝ)+1) * ρ^k * Real.sqrt n :=
        Finset.sum_le_sum hterm
    _ = 2*Real.sqrt (A+B) * Real.sqrt n * ∑ k ∈ Finset.range N, ((k:ℝ)+1)*ρ^k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ ≤ 2*Real.sqrt (A+B) * Real.sqrt n * (1/(1-ρ)^2) := by
        apply mul_le_mul_of_nonneg_left (arith_geom_partial_sum_le ρ hρ0 hρ1 N)
        positivity
    _ = 2*Real.sqrt (A+B) * (1/(1-ρ))^2 * Real.sqrt n := by
        rw [div_pow, one_pow]; ring

end

/-! ## The Finset-indexed wrapper: avoiding cross-round `Fin` merging

The inductive construction below needs to apply
`lemma8_partial_coloring_round` to a SHRINKING SUBSET of a FIXED index
type `Fin n` (never to a genuinely different `Fin m` at each level), so
that combining one round's result with the recursive call's result never
requires relating two unrelated `Fin` types — both live in `Fin n → ℝ`/
`Fin n → Bool` throughout, and the "active set" is tracked as a
`Finset (Fin n)` that only shrinks. This wrapper performs the (single,
local) `Finset ≃ Fin card` conversion needed to invoke Lemma 8, then
transports the result straight back to `Fin n`-indexed data. -/

noncomputable section

theorem lemma8_finset_round (n : ℕ) (S : Finset (Fin n)) (a : Fin n → Fin n → ℝ)
    (h01 : ∀ i j, a i j = 0 ∨ a i j = 1) (hS : 1 ≤ S.card) (lam : ℝ) (hlam : 2 ≤ lam)
    (hbudget : (n:ℝ) * ((12/Real.log 2) * Real.exp (-lam^2/4)) ≤ (S.card:ℝ)/10) :
    ∃ χ : Fin n → ℝ, (∀ j, χ j = 0 ∨ χ j = 1 ∨ χ j = -1) ∧ (∀ j, j ∉ S → χ j = 0) ∧
      2*(S.card/10) < (S.filter (fun j => χ j ≠ 0)).card ∧
      ∀ i : Fin n, |∑ j ∈ S, a i j * χ j| ≤ lam * Real.sqrt (S.card:ℝ) := by
  set e := S.equivFin with hedef
  set a' : Fin n → Fin S.card → ℝ := fun i k => a i ((e.symm k : ↥S) : Fin n) with ha'def
  have h01' : ∀ i (k : Fin S.card), a' i k = 0 ∨ a' i k = 1 := fun i k => h01 i _
  obtain ⟨x, y, hdist, hbound⟩ := lemma8_partial_coloring_round n a' h01' hS lam hlam hbudget
  set χ : Fin n → ℝ := fun j =>
    if hj : j ∈ S then (RSign x (e ⟨j, hj⟩) - RSign y (e ⟨j, hj⟩))/2 else 0 with hχdef
  have hinv1 : ∀ (j : Fin n) (hj : j ∈ S), ((e.symm (e ⟨j, hj⟩) : ↥S) : Fin n) = j :=
    fun j hj => congrArg Subtype.val (e.symm_apply_apply ⟨j, hj⟩)
  have hinv2 : ∀ (k : Fin S.card), e ⟨((e.symm k : ↥S) : Fin n), (e.symm k).2⟩ = k := by
    intro k
    have hcast : (⟨((e.symm k : ↥S) : Fin n), (e.symm k).2⟩ : ↥S) = e.symm k := Subtype.ext rfl
    rw [hcast]
    exact e.apply_symm_apply k
  refine ⟨χ, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ S
    · rw [hχdef]
      simp only [dif_pos hj]
      unfold RSign
      rcases x (e ⟨j, hj⟩) <;> rcases y (e ⟨j, hj⟩) <;> norm_num
    · rw [hχdef]; simp [dif_neg hj]
  · intro j hj
    rw [hχdef]; simp [dif_neg hj]
  · have hcard : (S.filter (fun j => χ j ≠ 0)).card
        = (univ.filter (fun k : Fin S.card => x k ≠ y k)).card := by
      apply Finset.card_bij' (i := fun j hj => e ⟨j, (Finset.mem_filter.mp hj).1⟩)
        (j := fun k _ => ((e.symm k : ↥S) : Fin n))
      case hi =>
        intro j hj
        have hjS : j ∈ S := (Finset.mem_filter.mp hj).1
        have hne : χ j ≠ 0 := (Finset.mem_filter.mp hj).2
        rw [hχdef] at hne
        simp only [dif_pos hjS] at hne
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        show x (e ⟨j, hjS⟩) ≠ y (e ⟨j, hjS⟩)
        intro heq
        apply hne
        unfold RSign
        rw [heq]
        ring
      case hj =>
        intro k hk
        have hxy : x k ≠ y k := (Finset.mem_filter.mp hk).2
        rw [Finset.mem_filter]
        refine ⟨(e.symm k).2, ?_⟩
        show χ ((e.symm k : ↥S) : Fin n) ≠ 0
        rw [hχdef]
        simp only [dif_pos (e.symm k).2]
        rw [hinv2]
        intro heq
        apply hxy
        rcases hxv : x k <;> rcases hyv : y k <;> simp_all [RSign] <;> norm_num at heq
      case left_inv =>
        intro j hj
        exact hinv1 j (Finset.mem_filter.mp hj).1
      case right_inv =>
        intro k _
        exact hinv2 k
    rw [hcard]
    exact hdist
  · intro i
    have heq : ∑ j ∈ S, a i j * χ j = ∑ k : Fin S.card, a' i k * ((RSign x k - RSign y k)/2) := by
      apply Finset.sum_bij' (i := fun j hj => e ⟨j, hj⟩) (j := fun k _ => ((e.symm k : ↥S) : Fin n))
      case hi => intro j _; exact Finset.mem_univ _
      case hj => intro k _; exact (e.symm k).2
      case left_neg => intro j hj; exact hinv1 j hj
      case right_neg => intro k _; exact hinv2 k
      case h =>
        intro j hj
        rw [ha'def, hχdef]
        simp only [dif_pos hj]
        rw [hinv1 j hj]
    rw [heq]
    exact hbound i

end

/-! ## The strong-induction construction

Repeatedly apply `lemma8_finset_round` on a shrinking `Finset (Fin n)`,
tracking the round index `k` against the idealized schedule `n·(9/10)^k`
so that `iterX_sum_le` bounds the total accumulated row-discrepancy by an
absolute (run-length-independent) multiple of `√n`. -/

noncomputable section

/-- `iterX n ·` is monotone increasing on `(0, n]`: writing
`C := 120n/log2`, `iterX n m = 2√(C · negMulLog(m/C))`, and since
`m/C ≤ n/C ≪ 1/e` throughout, this reduces to `negMulLog`'s known
monotonicity on `[0, 1/e]`. -/
lemma iterX_mono (n : ℝ) (hn : 0 < n) {m1 m2 : ℝ} (hm1 : 0 < m1) (hm12 : m1 ≤ m2)
    (hm2n : m2 ≤ n) : iterX n m1 ≤ iterX n m2 := by
  set C : ℝ := 120*n/Real.log 2 with hCdef
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hkey : ∀ m : ℝ, 0 < m → m ≤ n →
      iterX n m = 2 * Real.sqrt (C * Real.negMulLog (m / C)) := by
    intro m hm hmn
    have hCn : n ≤ C := by
      rw [hCdef, le_div_iff₀ hlog2pos]
      nlinarith [Real.log_two_lt_d9]
    have hmC : m ≤ C := hmn.trans hCn
    have hCm_ge1 : (1:ℝ) ≤ C/m := (one_le_div hm).mpr hmC
    have hlogCm_nonneg : 0 ≤ Real.log (C/m) := Real.log_nonneg hCm_ge1
    have hlogmC : Real.log (m/C) = - Real.log (C/m) := by
      rw [Real.log_div hm.ne' hCpos.ne', Real.log_div hCpos.ne' hm.ne']; ring
    have hCmC : C * Real.negMulLog (m / C) = m * Real.log (C / m) := by
      unfold Real.negMulLog
      rw [hlogmC]
      field_simp
    have heqarg : (120*n/(m*Real.log 2)) = C/m := by rw [hCdef]; ring
    unfold iterX iterLam
    rw [heqarg, mul_assoc, ← Real.sqrt_mul hlogCm_nonneg, mul_comm (Real.log (C/m)) m, ← hCmC]
  rw [hkey m1 hm1 (hm12.trans hm2n), hkey m2 (hm1.trans_le hm12) hm2n]
  have hlog2lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hexp1lt : Real.exp 1 < 120 := by linarith [Real.exp_one_lt_d9]
  have hnC_le : n / C ≤ Real.exp (-1) := by
    have hnC_eq : n / C = Real.log 2 / 120 := by rw [hCdef]; field_simp
    rw [hnC_eq, Real.exp_neg, inv_eq_one_div]
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 120) (Real.exp_pos 1)]
    nlinarith [mul_lt_mul_of_pos_right hlog2lt1 (Real.exp_pos 1), hexp1lt]
  have hm1_mem : m1/C ∈ Set.Icc (0:ℝ) (Real.exp (-1)) :=
    ⟨div_nonneg hm1.le hCpos.le, by
      have := div_le_div_of_nonneg_right (hm12.trans hm2n) hCpos.le
      linarith [this, hnC_le]⟩
  have hm2_mem : m2/C ∈ Set.Icc (0:ℝ) (Real.exp (-1)) :=
    ⟨div_nonneg (hm1.trans_le hm12).le hCpos.le, by
      have := div_le_div_of_nonneg_right hm2n hCpos.le
      linarith [this, hnC_le]⟩
  have hle : m1/C ≤ m2/C := by
    apply div_le_div_of_nonneg_right hm12 hCpos.le
  have hmono := negMulLog_strictMonoOn.monotoneOn hm1_mem hm2_mem hle
  have hmul : C * Real.negMulLog (m1/C) ≤ C * Real.negMulLog (m2/C) :=
    mul_le_mul_of_nonneg_left hmono hCpos.le
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmul) (by norm_num)

/-- Peel off rounds of `lemma8_finset_round` from a shrinking active
`Finset (Fin n)`, choosing `λ` FRESH from the actual current active size
each round (never from a pre-committed schedule), and tracking the round
index `k` against the idealized upper bound `n·(9/10)^k` on the actual
active size purely as a bookkeeping device for the final total. -/
theorem spencer_partial_coloring (n : ℕ) (hn : 0 < n) (a : Fin n → Fin n → ℝ)
    (h01 : ∀ i j, a i j = 0 ∨ a i j = 1) :
    ∀ m : ℕ, ∀ S : Finset (Fin n), S.card = m → ∀ k : ℕ,
      (m:ℝ) ≤ (n:ℝ) * (9/10)^k →
      ∃ (ε : Fin n → Bool) (K : ℕ),
        ∀ i, |∑ j ∈ S, a i j * RSign ε j|
          ≤ ∑ k' ∈ Finset.range K, iterX (n:ℝ) ((n:ℝ) * (9/10)^(k+k')) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro S hScard k hk
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · refine ⟨fun _ => true, 0, ?_⟩
      have hSempty : S = ∅ := Finset.card_eq_zero.mp (by rw [hScard]; exact hm0)
      intro i
      simp [hSempty]
    · have hmn : m ≤ n := by
        have h1 : S.card ≤ n := by
          have h2 := Finset.card_le_univ S
          rwa [Fintype.card_fin] at h2
        rw [hScard] at h1; exact h1
      have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hmpos
      have hmnR : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      set lam : ℝ := iterLam (n:ℝ) (m:ℝ) with hlamdef
      have hlam2 : 2 ≤ lam := by
        have hstep : (120:ℝ)/Real.log 2 ≤ 120*(n:ℝ)/((m:ℝ)*Real.log 2) := by
          rw [div_le_div_iff₀ hlog2pos (mul_pos hmR hlog2pos)]
          nlinarith [mul_le_mul_of_nonneg_right hmnR hlog2pos.le]
        have h120 : Real.exp 1 ≤ (120:ℝ)/Real.log 2 := by
          rw [le_div_iff₀ hlog2pos]
          have hp : Real.exp 1 * Real.log 2 < 2.7182818286 * 0.6931471808 :=
            mul_lt_mul'' Real.exp_one_lt_d9 Real.log_two_lt_d9 (Real.exp_pos 1).le hlog2pos.le
          nlinarith [hp]
        have harg : Real.exp 1 ≤ 120*(n:ℝ)/((m:ℝ)*Real.log 2) := h120.trans hstep
        have hlog_ge1 : (1:ℝ) ≤ Real.log (120*(n:ℝ)/((m:ℝ)*Real.log 2)) := by
          have := Real.log_le_log (Real.exp_pos 1) harg
          rwa [Real.log_exp] at this
        have hsqrt_ge1 : (1:ℝ) ≤ Real.sqrt (Real.log (120*(n:ℝ)/((m:ℝ)*Real.log 2))) := by
          rw [show (1:ℝ) = Real.sqrt 1 by simp]
          exact Real.sqrt_le_sqrt hlog_ge1
        rw [hlamdef]; unfold iterLam; linarith [hsqrt_ge1]
      have hbudgetS : (n:ℝ) * ((12/Real.log 2) * Real.exp (-lam^2/4)) ≤ (S.card:ℝ)/10 := by
        rw [hScard, hlamdef]
        exact le_of_eq (iterLam_budget_eq (n:ℝ) (m:ℝ) hnR hmR hmnR)
      have hScard1 : 1 ≤ S.card := by rw [hScard]; exact hmpos
      obtain ⟨χ, hχ013, hχsupp, hdist, hbound⟩ :=
        lemma8_finset_round n S a h01 hScard1 lam hlam2 hbudgetS
      classical
      set S' : Finset (Fin n) := S.filter (fun j => χ j = 0) with hS'def
      have hpart_card : S'.card + (S.filter (fun j => ¬ (χ j = 0))).card = S.card :=
        Finset.card_filter_add_card_filter_not (s := S) (fun j => χ j = 0)
      have hdist' : 2*(S.card/10) < (S.filter (fun j => ¬ (χ j = 0))).card := hdist
      have hS'card_lt' : S'.card < S.card := by omega
      have hshrink : 10 * S'.card ≤ 9 * S.card := by omega
      have hS'card_lt : S'.card < m := by rw [← hScard]; exact hS'card_lt'
      have hshrinkR : (S'.card:ℝ) ≤ (9/10) * (S.card:ℝ) := by
        have h10 : (10:ℝ) * (S'.card:ℝ) ≤ 9 * (S.card:ℝ) := by exact_mod_cast hshrink
        linarith
      have hS'k1 : (S'.card:ℝ) ≤ (n:ℝ) * (9/10)^(k+1) := by
        calc (S'.card:ℝ) ≤ (9/10) * (S.card:ℝ) := hshrinkR
          _ = (9/10) * (m:ℝ) := by rw [hScard]
          _ ≤ (9/10) * ((n:ℝ)*(9/10)^k) := by nlinarith [hk]
          _ = (n:ℝ) * (9/10)^(k+1) := by ring
      obtain ⟨ε', K', hbound'⟩ := IH S'.card hS'card_lt S' rfl (k+1) hS'k1
      set ε : Fin n → Bool := fun j => if χ j = 0 then ε' j else decide (χ j = 1) with hεdef
      refine ⟨ε, K'+1, ?_⟩
      intro i
      have hcolored_eq : ∀ j ∈ S.filter (fun j => ¬ (χ j = 0)), RSign ε j = χ j := by
        intro j hj
        have hjne : ¬ (χ j = 0) := (Finset.mem_filter.mp hj).2
        have hεj : ε j = decide (χ j = 1) := by rw [hεdef]; simp [hjne]
        unfold RSign
        rw [hεj]
        rcases hχ013 j with h1 | h1 | h1
        · exact absurd h1 hjne
        · norm_num [h1]
        · norm_num [h1]
      have hS'_eq : ∀ j ∈ S', RSign ε j = RSign ε' j := by
        intro j hj
        have hjeq0 : χ j = 0 := (Finset.mem_filter.mp hj).2
        have hεj : ε j = ε' j := by rw [hεdef]; simp [hjeq0]
        unfold RSign
        rw [hεj]
      have hsum_colored_eq : ∑ j ∈ S.filter (fun j => ¬ (χ j = 0)), a i j * RSign ε j
          = ∑ j ∈ S.filter (fun j => ¬ (χ j = 0)), a i j * χ j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcolored_eq j hj]
      have hsum_S'_eq : ∑ j ∈ S', a i j * RSign ε j = ∑ j ∈ S', a i j * RSign ε' j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hS'_eq j hj]
      have hsplit : ∑ j ∈ S', a i j * RSign ε j
            + ∑ j ∈ S.filter (fun j => ¬ (χ j = 0)), a i j * RSign ε j
          = ∑ j ∈ S, a i j * RSign ε j :=
        Finset.sum_filter_add_sum_filter_not S (fun j => χ j = 0) (fun j => a i j * RSign ε j)
      have hzero_on_S' : ∀ j ∈ S', a i j * χ j = 0 := by
        intro j hj
        have hjeq0 : χ j = 0 := (Finset.mem_filter.mp hj).2
        rw [hjeq0, mul_zero]
      have hsum_split_χ : ∑ j ∈ S.filter (fun j => ¬ (χ j = 0)), a i j * χ j
          = ∑ j ∈ S, a i j * χ j := by
        have hh := Finset.sum_filter_add_sum_filter_not S (fun j => χ j = 0) (fun j => a i j * χ j)
        rw [Finset.sum_eq_zero hzero_on_S'] at hh
        linarith [hh]
      have hkey_eq : ∑ j ∈ S, a i j * RSign ε j
          = ∑ j ∈ S, a i j * χ j + ∑ j ∈ S', a i j * RSign ε' j := by
        rw [← hsplit, hsum_S'_eq, hsum_colored_eq, hsum_split_χ]
        ring
      rw [hkey_eq]
      have habs : |∑ j ∈ S, a i j * χ j + ∑ j ∈ S', a i j * RSign ε' j|
          ≤ |∑ j ∈ S, a i j * χ j| + |∑ j ∈ S', a i j * RSign ε' j| := abs_add_le _ _
      refine habs.trans ?_
      have h1 : |∑ j ∈ S, a i j * χ j| ≤ lam * Real.sqrt (S.card:ℝ) := hbound i
      have h2 : |∑ j ∈ S', a i j * RSign ε' j|
          ≤ ∑ k'' ∈ Finset.range K', iterX (n:ℝ) ((n:ℝ) * (9/10)^(k+1+k'')) := hbound' i
      have h3 : lam * Real.sqrt (S.card:ℝ) = iterX (n:ℝ) (m:ℝ) := by
        rw [hlamdef]; unfold iterX; rw [hScard]
      have hpow_le1 : ((9:ℝ)/10)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hm2n : (n:ℝ)*(9/10)^k ≤ (n:ℝ) := by nlinarith [hpow_le1, hnR]
      have h4 : iterX (n:ℝ) (m:ℝ) ≤ iterX (n:ℝ) ((n:ℝ)*(9/10)^k) :=
        iterX_mono (n:ℝ) hnR hmR hk hm2n
      have heqsum : ∑ k'' ∈ Finset.range K', iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+1+k''))
          = ∑ k' ∈ Finset.range K', iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+(k'+1))) := by
        apply Finset.sum_congr rfl
        intro k' _
        have heq : k+1+k' = k+(k'+1) := by ring
        rw [heq]
      have h5 : iterX (n:ℝ) ((n:ℝ)*(9/10)^k)
            + ∑ k'' ∈ Finset.range K', iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+1+k''))
          = ∑ k' ∈ Finset.range (K'+1), iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+k')) := by
        rw [Finset.sum_range_succ', heqsum]
        have heq0 : k+0 = k := by ring
        rw [heq0]
        ring
      calc |∑ j ∈ S, a i j * χ j| + |∑ j ∈ S', a i j * RSign ε' j|
          ≤ lam * Real.sqrt (S.card:ℝ)
              + ∑ k'' ∈ Finset.range K', iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+1+k'')) :=
            add_le_add h1 h2
        _ = iterX (n:ℝ) (m:ℝ)
              + ∑ k'' ∈ Finset.range K', iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+1+k'')) := by rw [h3]
        _ ≤ iterX (n:ℝ) ((n:ℝ)*(9/10)^k)
              + ∑ k'' ∈ Finset.range K', iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+1+k'')) := by
            linarith [h4]
        _ = ∑ k' ∈ Finset.range (K'+1), iterX (n:ℝ) ((n:ℝ)*(9/10)^(k+k')) := h5

/-- Final assembly: for an `n×n` `{0,1}`-matrix, there is a `±1` coloring
whose signed row sums are all bounded by an explicit, `n`-independent
multiple of `√n`. -/
theorem spencer_sqrt_n_coloring (n : ℕ) (hn : 0 < n) (a : Fin n → Fin n → ℝ)
    (h01 : ∀ i j, a i j = 0 ∨ a i j = 1) :
    ∃ ε : Fin n → Bool, ∀ i, |∑ j, a i j * RSign ε j|
      ≤ 2 * Real.sqrt (Real.log (120/Real.log 2) + Real.log (10/9))
          * (1 / (1 - Real.sqrt (9/10)))^2 * Real.sqrt (n:ℝ) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hk0 : (n:ℝ) ≤ (n:ℝ) * (9/10)^(0:ℕ) := by norm_num
  obtain ⟨ε, K, hK⟩ := spencer_partial_coloring n hn a h01 n Finset.univ (by simp) 0 hk0
  refine ⟨ε, ?_⟩
  intro i
  have h1 : |∑ j ∈ (Finset.univ : Finset (Fin n)), a i j * RSign ε j|
      ≤ ∑ k' ∈ Finset.range K, iterX (n:ℝ) ((n:ℝ)*(9/10)^(0+k')) := hK i
  have h2 : ∑ k' ∈ Finset.range K, iterX (n:ℝ) ((n:ℝ)*(9/10)^(0+k'))
      = ∑ k' ∈ Finset.range K, iterX (n:ℝ) ((n:ℝ)*(9/10)^k') := by
    apply Finset.sum_congr rfl; intro k' _; norm_num
  rw [h2] at h1
  exact h1.trans (iterX_sum_le (n:ℝ) hn0 K)

end


/-- Final result: there is a single constant `C` such that for every
`n×n` `{0,1}`-matrix, some `±1` coloring keeps every row's signed sum
within `C·√n`. -/
theorem solution :
    ∃ C : ℝ, ∀ (n : ℕ), 0 < n → ∀ (A : Fin n → Fin n → ℝ),
      (∀ i j, A i j = 0 ∨ A i j = 1) →
      ∃ ε : Fin n → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
        ∀ i, |∑ j, A i j * ε j| ≤ C * Real.sqrt (n : ℝ) := by
  refine ⟨2 * Real.sqrt (Real.log (120/Real.log 2) + Real.log (10/9))
          * (1 / (1 - Real.sqrt (9/10)))^2, ?_⟩
  intro n hn A h01
  obtain ⟨ε, hε⟩ := spencer_sqrt_n_coloring n hn A h01
  refine ⟨fun j => RSign ε j, fun j => ?_, hε⟩
  dsimp only [RSign]
  split <;> simp
