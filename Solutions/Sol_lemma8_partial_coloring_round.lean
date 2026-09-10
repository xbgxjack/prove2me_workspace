import Mathlib
import Definitions.Def_RSign
import Definitions.Def_rowSumB
import Definitions.Def_shellIdx
import Definitions.Def_shellFin
import Theorems.Thm_shannonEntropy_shellFin_le
import Theorems.Thm_shannonEntropy_pi_le
import Theorems.Thm_shannonEntropy_pigeonhole
import Theorems.Thm_choose_sum_le_exp_mul_binEntropy
import Theorems.Thm_kleitman_diameter

open Finset

/-! This solution reduces to Lemma 9 (`shannonEntropy_shellFin_le`, currently
Open — imported here as a hypothesis of the joint pigeonhole/Kleitman
argument) plus four already-Proved platform theorems. It reproduces
Rothvoß's assembly of his Lemma 8 (the one-round partial-coloring lemma)
from Lemma 9, subadditivity of entropy across rows, a Pinsker-type bound on
the binary entropy function, and Kleitman's diameter theorem. -/

theorem binEntropy_le_log_two_sub_sq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.binEntropy p ≤ Real.log 2 - 2 * (p - 1/2)^2 := by
  set g : ℝ → ℝ := fun p => Real.binEntropy p + 2 * (p - 1/2)^2 with hg_def
  have hgcont : ContinuousOn g (Set.Icc 0 1) := by
    apply Continuous.continuousOn
    simp only [hg_def]
    fun_prop
  have hgdiff : DifferentiableOn ℝ g (interior (Set.Icc (0:ℝ) 1)) := by
    rw [interior_Icc]
    intro p hp
    rw [Set.mem_Ioo] at hp
    apply DifferentiableAt.differentiableWithinAt
    simp only [hg_def]
    apply DifferentiableAt.add
    · exact Real.differentiableAt_binEntropy hp.1.ne' hp.2.ne
    · fun_prop
  have hderiv_eq : ∀ p ∈ Set.Ioo (0:ℝ) 1, deriv g p = Real.log (1-p) - Real.log p + 4*(p - 1/2) := by
    intro p hp
    rw [Set.mem_Ioo] at hp
    have hbin : HasDerivAt Real.binEntropy (Real.log (1-p) - Real.log p) p :=
      Real.hasDerivAt_binEntropy hp.1.ne' hp.2.ne
    have hquad : HasDerivAt (fun p : ℝ => 2*(p-1/2)^2) (4*(p-1/2)) p := by
      have h1 : HasDerivAt (fun p : ℝ => p - 1/2) 1 p := (hasDerivAt_id p).sub_const _
      have h2 := (h1.fun_pow 2).const_mul (2:ℝ)
      norm_num at h2
      have hval : (4:ℝ) * (p - 1/2) = 2 * (2 * (p - 1/2)) := by ring
      rw [hval]
      exact h2
    have hg' : HasDerivAt g (Real.log (1-p) - Real.log p + 4*(p-1/2)) p := by
      rw [hg_def]; exact hbin.add hquad
    exact hg'.deriv
  have hgdiff' : DifferentiableOn ℝ (deriv g) (interior (Set.Icc (0:ℝ) 1)) := by
    rw [interior_Icc]
    have hmodel : DifferentiableOn ℝ
        (fun p => Real.log (1-p) - Real.log p + 4*(p - 1/2)) (Set.Ioo (0:ℝ) 1) := by
      intro p hp
      rw [Set.mem_Ioo] at hp
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.add
      · apply DifferentiableAt.sub
        · fun_prop (disch := linarith)
        · fun_prop (disch := linarith)
      · fun_prop
    exact hmodel.congr (fun p hp => hderiv_eq p hp)
  have hderiv2_nonpos : ∀ p ∈ interior (Set.Icc (0:ℝ) 1), deriv^[2] g p ≤ 0 := by
    rw [interior_Icc]
    intro p hp
    rw [Set.mem_Ioo] at hp
    have heq2 : deriv^[2] g p = deriv (fun p => Real.log (1-p) - Real.log p + 4*(p - 1/2)) p := by
      rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply]
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [IsOpen.mem_nhds isOpen_Ioo hp] with x hx
      exact hderiv_eq x hx
    rw [heq2]
    have hd1 : HasDerivAt (fun p : ℝ => Real.log (1-p)) (-(1-p)⁻¹) p := by
      have h1 : HasDerivAt (fun p : ℝ => (1:ℝ) - p) (-1) p := by
        simpa using (hasDerivAt_id p).const_sub (1:ℝ)
      have h2 := h1.log (show (1:ℝ) - p ≠ 0 by linarith)
      convert h2 using 1
      field_simp
    have hd2 : HasDerivAt (fun p : ℝ => Real.log p) p⁻¹ p := Real.hasDerivAt_log hp.1.ne'
    have hd3 : HasDerivAt (fun p : ℝ => (4:ℝ)*(p - 1/2)) 4 p := by
      have h1 : HasDerivAt (fun p : ℝ => p - 1/2) 1 p := (hasDerivAt_id p).sub_const _
      simpa using h1.const_mul (4:ℝ)
    have hsum : HasDerivAt (fun p => Real.log (1-p) - Real.log p + 4*(p - 1/2))
        (-(1-p)⁻¹ - p⁻¹ + 4) p := (hd1.sub hd2).add hd3
    rw [hsum.deriv]
    have h14 : p * (1-p) ≤ 1/4 := by nlinarith [sq_nonneg (p - 1/2)]
    have hppos : 0 < p := hp.1
    have h1ppos : 0 < 1 - p := by linarith [hp.2]
    have hinv : 4 ≤ (1-p)⁻¹ + p⁻¹ := by
      rw [inv_add_inv h1ppos.ne' hppos.ne']
      rw [le_div_iff₀ (by positivity)]
      nlinarith [h14]
    linarith [hinv]
  have hconcave : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) g :=
    concaveOn_of_deriv2_nonpos (convex_Icc 0 1) hgcont hgdiff hgdiff' hderiv2_nonpos
  have hsymm : ∀ q ∈ Set.Icc (0:ℝ) 1, g (1 - q) = g q := by
    intro q _
    simp only [hg_def]
    rw [Real.binEntropy_one_sub]
    ring_nf
  have hg_half : g (1/2) = Real.log 2 := by
    simp only [hg_def]
    rw [show (1:ℝ)/2 - 1/2 = 0 by ring]
    simp [Real.binEntropy_two_inv]
  have key : g p ≤ Real.log 2 := by
    rcases lt_trichotomy p (1/2) with hlt | heq | hgt
    · have hx : p ∈ Set.Icc (0:ℝ) 1 := ⟨hp0, hp1⟩
      have hz : (1:ℝ) - p ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith
      have hyz : (1:ℝ)/2 < 1 - p := by linarith
      have hslope := hconcave.slope_anti_adjacent hx hz hlt hyz
      rw [hsymm p ⟨hp0, hp1⟩, show (1:ℝ) - p - 1/2 = 1/2 - p from by ring] at hslope
      have hpos : (0:ℝ) < 1/2 - p := by linarith
      rw [div_le_div_iff_of_pos_right hpos] at hslope
      rw [hg_half] at hslope
      linarith
    · rw [heq, hg_half]
    · have hx : (1:ℝ) - p ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith
      have hz : p ∈ Set.Icc (0:ℝ) 1 := ⟨hp0, hp1⟩
      have hxy : (1:ℝ) - p < 1/2 := by linarith
      have hslope := hconcave.slope_anti_adjacent hx hz hxy hgt
      rw [hsymm p ⟨hp0, hp1⟩, show (1:ℝ)/2 - (1 - p) = p - 1/2 from by ring] at hslope
      have hpos : (0:ℝ) < p - 1/2 := by linarith
      rw [div_le_div_iff_of_pos_right hpos] at hslope
      rw [hg_half] at hslope
      linarith
  simp only [hg_def] at key
  linarith [key]


variable {m : ℕ} (Δ : ℝ)

lemma abs_rowSumB_le (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1) (χ : Fin m → Bool) :
    |rowSumB a χ| ≤ m := by
  unfold rowSumB
  calc |∑ j, a j * RSign χ j| ≤ ∑ j, |a j * RSign χ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin m, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        have ha : |a j| ≤ 1 := by rcases h01 j with h | h <;> rw [h] <;> norm_num
        have hs : |RSign χ j| = 1 := by unfold RSign; split <;> norm_num
        rw [hs, mul_one]
        exact ha
    _ = m := by simp

lemma shellIdx_dist (a : Fin m → ℝ) (ω : Fin m → Bool) (hΔpos : 0 < Δ) :
    |rowSumB a ω - 2*Δ*(shellIdx Δ a ω : ℝ)| ≤ Δ := by
  have h := abs_sub_round (rowSumB a ω / (2*Δ))
  unfold shellIdx
  have heq : rowSumB a ω - 2*Δ*(round (rowSumB a ω / (2*Δ)) : ℝ)
      = (2*Δ) * (rowSumB a ω / (2*Δ) - round (rowSumB a ω / (2*Δ))) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Δ)]
  calc 2*Δ * |rowSumB a ω / (2*Δ) - round (rowSumB a ω / (2*Δ))|
      ≤ 2*Δ * (1/2) := by
        apply mul_le_mul_of_nonneg_left h (by positivity)
    _ = Δ := by ring

lemma shellIdx_bound (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1) (hΔ : (1:ℝ)/2 ≤ Δ)
    (ω : Fin m → Bool) :
    (shellIdx Δ a ω : ℝ) ∈ Set.Icc (-((m:ℝ)/(2*Δ) + 1)) ((m:ℝ)/(2*Δ) + 1) := by
  have hΔpos : 0 < Δ := by linarith
  have hb := abs_rowSumB_le a h01 ω
  have hd := shellIdx_dist Δ a ω hΔpos
  rw [abs_le] at hb hd
  have hub : 2*Δ*(shellIdx Δ a ω:ℝ) ≤ (m:ℝ) + 2*Δ := by nlinarith [hb.2, hd.1]
  have hlb : -((m:ℝ) + 2*Δ) ≤ 2*Δ*(shellIdx Δ a ω:ℝ) := by nlinarith [hb.1, hd.2]
  rw [Set.mem_Icc]
  constructor
  · have hstep : (-(shellIdx Δ a ω:ℝ) - 1) * (2*Δ) ≤ (m:ℝ) := by nlinarith [hlb]
    have h2 : -(shellIdx Δ a ω:ℝ) - 1 ≤ (m:ℝ)/(2*Δ) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*Δ)]; exact hstep
    linarith [h2]
  · have hstep : ((shellIdx Δ a ω:ℝ) - 1) * (2*Δ) ≤ (m:ℝ) := by nlinarith [hub]
    have h2 : (shellIdx Δ a ω:ℝ) - 1 ≤ (m:ℝ)/(2*Δ) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*Δ)]; exact hstep
    linarith [h2]

/-- The shell index, packaged into a fixed-size `Fin` type via a shift and a
(never-triggered, for `Δ ≥ 1/2`) safety `%`. -/

lemma shellIdx_shift_range (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1)
    (hΔ : (1:ℝ)/2 ≤ Δ) (ω : Fin m → Bool) :
    0 ≤ shellIdx Δ a ω + (m+1) ∧ (shellIdx Δ a ω + (m+1)).toNat < 2*m+3 := by
  have hb := shellIdx_bound Δ a h01 hΔ ω
  rw [Set.mem_Icc] at hb
  have hle : (m:ℝ)/(2*Δ) ≤ m := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2*Δ)]
    nlinarith [hΔ, (Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hub : (shellIdx Δ a ω : ℝ) ≤ m + 1 := by linarith [hb.2, hle]
  have hlb : -(((m:ℝ)) + 1) ≤ (shellIdx Δ a ω : ℝ) := by linarith [hb.1, hle]
  have hub' : shellIdx Δ a ω ≤ (m:ℤ) + 1 := by exact_mod_cast hub
  have hlb' : -((m:ℤ) + 1) ≤ shellIdx Δ a ω := by exact_mod_cast hlb
  omega

lemma shellFin_eq_toNat (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1)
    (hΔ : (1:ℝ)/2 ≤ Δ) (ω : Fin m → Bool) :
    (shellFin Δ a ω : ℕ) = (shellIdx Δ a ω + (m+1)).toNat := by
  obtain ⟨_, hsmall⟩ := shellIdx_shift_range Δ a h01 hΔ ω
  unfold shellFin
  simp only
  exact Nat.mod_eq_of_lt hsmall

lemma shellFin_eq_iff (a : Fin m → ℝ) (h01 : ∀ j, a j = 0 ∨ a j = 1)
    (hΔ : (1:ℝ)/2 ≤ Δ) (ω : Fin m → Bool) (k : Fin (2*m+3)) :
    shellFin Δ a ω = k ↔ shellIdx Δ a ω = (k : ℤ) - (m+1) := by
  obtain ⟨hnn, _⟩ := shellIdx_shift_range Δ a h01 hΔ ω
  rw [Fin.ext_iff, shellFin_eq_toNat Δ a h01 hΔ ω]
  constructor
  · intro h; omega
  · intro h; omega

theorem solution (n : ℕ) (a : Fin n → Fin m → ℝ)
    (h01 : ∀ i j, a i j = 0 ∨ a i j = 1) (hm : 1 ≤ m) (lam : ℝ) (hlam : 2 ≤ lam)
    (hbudget : (n:ℝ) * ((12 / Real.log 2) * Real.exp (-lam^2/4)) ≤ (m:ℝ)/10) :
    ∃ x y : Fin m → Bool,
      2 * (m/10) < (univ.filter (fun j => x j ≠ y j)).card ∧
      ∀ i : Fin n, |∑ j, a i j * ((RSign x j - RSign y j)/2)| ≤ lam * Real.sqrt (m:ℝ) := by
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Δ : ℝ := lam * Real.sqrt (m:ℝ) with hΔdef
  have hsqrtm1 : (1:ℝ) ≤ Real.sqrt (m:ℝ) := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hmR
  have hΔge : lam ≤ Δ := by rw [hΔdef]; nlinarith [hsqrtm1]
  have hΔ : (1:ℝ)/2 ≤ Δ := by linarith
  have hΔpos : 0 < Δ := by linarith
  -- The joint (all-n-rows) quantized shell-vector and its entropy bound.
  set Z : Fin n → (Fin m → Bool) → Fin (2*m+3) := fun i χ => shellFin Δ (a i) χ with hZdef
  set Z' : (Fin m → Bool) → (Fin n → Fin (2*m+3)) := fun χ i => Z i χ with hZ'def
  have hH : shannonEntropy Z' ≤ (m:ℝ)/10 := by
    have hjoint : shannonEntropy Z' ≤ ∑ i, shannonEntropy (Z i) := shannonEntropy_pi_le Z
    have hrow : ∀ i : Fin n, shannonEntropy (Z i) ≤ (12/Real.log 2) * Real.exp (-lam^2/4) :=
      fun i => shannonEntropy_shellFin_le hm (a i) (h01 i) lam hlam
    have hsum_le : ∑ i : Fin n, shannonEntropy (Z i)
        ≤ (n:ℝ) * ((12/Real.log 2) * Real.exp (-lam^2/4)) := by
      calc ∑ i : Fin n, shannonEntropy (Z i)
          ≤ ∑ _i : Fin n, (12/Real.log 2) * Real.exp (-lam^2/4) :=
            Finset.sum_le_sum (fun i _ => hrow i)
        _ = (n:ℝ) * ((12/Real.log 2) * Real.exp (-lam^2/4)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    linarith [hjoint, hsum_le, hbudget]
  -- Pigeonhole: some bucket `b` has an exponentially large fiber `A`.
  have : Nonempty (Fin n → Fin (2*m+3)) := ⟨fun _ => ⟨0, by omega⟩⟩
  obtain ⟨b, hb⟩ := shannonEntropy_pigeonhole Z'
  set A : Finset (Fin m → Bool) := univ.filter (fun χ => Z' χ = b) with hAdef
  have hcardΩ : (Fintype.card (Fin m → Bool) : ℝ) = Real.exp ((m:ℝ) * Real.log 2) := by
    have h1 : Fintype.card (Fin m → Bool) = 2^m := by rw [Fintype.card_fun]; simp
    have h2 : Real.exp ((m:ℝ) * Real.log 2) = (2:ℝ)^m := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    rw [h1, h2]
    push_cast
    ring
  have hrpow : (2:ℝ)^(-shannonEntropy Z') = Real.exp (-shannonEntropy Z' * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), mul_comm]
  have hAcard_ge : Real.exp (((m:ℝ) - shannonEntropy Z') * Real.log 2) ≤ (A.card : ℝ) := by
    have hb' := hb
    rw [hcardΩ, hrpow, ← Real.exp_add] at hb'
    rwa [show (m:ℝ) * Real.log 2 + -shannonEntropy Z' * Real.log 2
        = ((m:ℝ) - shannonEntropy Z') * Real.log 2 by ring] at hb'
  have hAcard_ge2 : Real.exp ((9*(m:ℝ)/10) * Real.log 2) ≤ (A.card : ℝ) := by
    calc Real.exp ((9*(m:ℝ)/10) * Real.log 2)
        ≤ Real.exp (((m:ℝ) - shannonEntropy Z') * Real.log 2) := by
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_right _ hlog2pos.le
          linarith [hH]
      _ ≤ (A.card : ℝ) := hAcard_ge
  -- Kleitman's diameter theorem, via a binEntropy bound on the choose-sum.
  set s : ℕ := m / 10 with hsdef
  have hsm : (10:ℕ) * s ≤ m := by rw [hsdef, mul_comm]; exact Nat.div_mul_le_self m 10
  have h2sm : 2 * s < m := by omega
  have hchooseR : (∑ i ∈ Finset.range (s + 1), (m.choose i : ℝ))
      ≤ Real.exp ((m:ℝ) * Real.binEntropy ((s:ℝ)/m)) :=
    choose_sum_le_exp_mul_binEntropy m s hm (by omega)
  have hsm_ratio : (s:ℝ)/(m:ℝ) ≤ 1/10 := by
    rw [div_le_div_iff₀ hmpos (by norm_num : (0:ℝ) < 10)]
    have h10s : ((10*s : ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast hsm
    push_cast at h10s
    linarith [h10s]
  have hsm_nonneg : (0:ℝ) ≤ (s:ℝ)/(m:ℝ) := by positivity
  have hsm_le1 : (s:ℝ)/(m:ℝ) ≤ 1 := by linarith [hsm_ratio]
  have hbin_le : Real.binEntropy ((s:ℝ)/m) ≤ Real.log 2 - 2*((s:ℝ)/m - 1/2)^2 :=
    binEntropy_le_log_two_sub_sq ((s:ℝ)/m) hsm_nonneg hsm_le1
  have hsq_ge : (0.4:ℝ)^2 ≤ ((s:ℝ)/m - 1/2)^2 := by nlinarith [hsm_ratio]
  have hbin_lt : Real.binEntropy ((s:ℝ)/m) < (9/10) * Real.log 2 := by
    have hlog2_bd : Real.log 2 < 3.2 := by linarith [Real.log_two_lt_d9]
    nlinarith [hbin_le, hsq_ge, hlog2_bd]
  have hexp_lt : Real.exp ((m:ℝ) * Real.binEntropy ((s:ℝ)/m))
      < Real.exp ((9*(m:ℝ)/10) * Real.log 2) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_lt_mul_of_pos_left hbin_lt hmpos]
  have hchoose_lt : (∑ i ∈ Finset.range (s + 1), (m.choose i : ℝ)) < (A.card : ℝ) :=
    lt_of_le_of_lt hchooseR hexp_lt |>.trans_le hAcard_ge2
  have hchoose_lt_nat : (∑ i ∈ Finset.range (s + 1), m.choose i) < A.card := by
    exact_mod_cast hchoose_lt
  have hcardι : Fintype.card (Fin m) = m := Fintype.card_fin m
  have hAhyp : (∑ i ∈ Finset.range (s + 1), (Fintype.card (Fin m)).choose i) < A.card := by
    rwa [hcardι]
  have hsι : 2 * s < Fintype.card (Fin m) := by rwa [hcardι]
  obtain ⟨x, hxA, y, hyA, hdist⟩ := kleitman_diameter s hsι A hAhyp
  refine ⟨x, y, hdist, ?_⟩
  have hxmem : ∀ i, shellFin Δ (a i) x = b i := by
    intro i
    have hx := hxA
    rw [hAdef, Finset.mem_filter] at hx
    exact congrFun hx.2 i
  have hymem : ∀ i, shellFin Δ (a i) y = b i := by
    intro i
    have hy := hyA
    rw [hAdef, Finset.mem_filter] at hy
    exact congrFun hy.2 i
  intro i
  have heqshell : shellFin Δ (a i) x = shellFin Δ (a i) y := by rw [hxmem i, hymem i]
  have heqidx : shellIdx Δ (a i) x = shellIdx Δ (a i) y := by
    have h1 : shellIdx Δ (a i) x = (shellFin Δ (a i) x : ℤ) - (m+1) :=
      (shellFin_eq_iff Δ (a i) (h01 i) hΔ x (shellFin Δ (a i) x)).mp rfl
    have h2 : shellIdx Δ (a i) y = (shellFin Δ (a i) y : ℤ) - (m+1) :=
      (shellFin_eq_iff Δ (a i) (h01 i) hΔ y (shellFin Δ (a i) y)).mp rfl
    rw [h1, h2, heqshell]
  have hdx := shellIdx_dist Δ (a i) x hΔpos
  have hdy := shellIdx_dist Δ (a i) y hΔpos
  rw [heqidx] at hdx
  have hdiff : |rowSumB (a i) x - rowSumB (a i) y| ≤ 2*Δ := by
    have htri := abs_sub_le (rowSumB (a i) x) (2*Δ*(shellIdx Δ (a i) y:ℝ)) (rowSumB (a i) y)
    have hcomm : |2*Δ*(shellIdx Δ (a i) y:ℝ) - rowSumB (a i) y|
        = |rowSumB (a i) y - 2*Δ*(shellIdx Δ (a i) y:ℝ)| := abs_sub_comm _ _
    rw [hcomm] at htri
    calc |rowSumB (a i) x - rowSumB (a i) y|
        ≤ |rowSumB (a i) x - 2*Δ*(shellIdx Δ (a i) y:ℝ)|
          + |rowSumB (a i) y - 2*Δ*(shellIdx Δ (a i) y:ℝ)| := htri
      _ ≤ Δ + Δ := add_le_add hdx hdy
      _ = 2*Δ := by ring
  have hrel : rowSumB (a i) x - rowSumB (a i) y
      = 2 * ∑ j, a i j * ((RSign x j - RSign y j)/2) := by
    unfold rowSumB
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hrel, abs_mul, show |(2:ℝ)| = 2 from by norm_num] at hdiff
  linarith [hdiff]

