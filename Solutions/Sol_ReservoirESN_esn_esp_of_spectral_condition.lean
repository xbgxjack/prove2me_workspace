import Theorems.Thm_ReservoirESN_esp_of_contracting
import Definitions.Def_ReservoirESN
open ReservoirESN Matrix

private noncomputable def Fmap {n N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (Cin : Matrix (Fin N) (Fin n) ℝ)
    (ζ : EuclideanSpace ℝ (Fin N)) (σ : ℝ → ℝ)
    (v : EuclideanSpace ℝ (Fin N)) (w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm
    (fun i => σ ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
      + Cin *ᵥ (EuclideanSpace.equiv (Fin n) ℝ w)) i + ζ i))

private theorem Fmap_apply {n N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (Cin : Matrix (Fin N) (Fin n) ℝ)
    (ζ : EuclideanSpace ℝ (Fin N)) (σ : ℝ → ℝ)
    (v : EuclideanSpace ℝ (Fin N)) (w : EuclideanSpace ℝ (Fin n)) (i : Fin N) :
    Fmap A Cin ζ σ v w i = σ ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
      + Cin *ᵥ (EuclideanSpace.equiv (Fin n) ℝ w)) i + ζ i) := rfl

private theorem isSolution_iff_isESNSolution {n N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (Cin : Matrix (Fin N) (Fin n) ℝ) (ζ : EuclideanSpace ℝ (Fin N)) (σ : ℝ → ℝ)
    (z : ℕ → EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin N)) :
    IsSolution (Fmap A Cin ζ σ) z x ↔ IsESNSolution A Cin ζ σ z x := by
  constructor
  · intro h k i
    have := h k
    rw [this, Fmap_apply]
  · intro h k
    apply PiLp.ext
    intro i
    rw [Fmap_apply]
    exact h k i

private theorem norm_le_sqrt_of_forall_abs_le {N : ℕ} (y : EuclideanSpace ℝ (Fin N))
    (h : ∀ i, |y i| ≤ 1) : ‖y‖ ≤ Real.sqrt N := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hyi : ‖y i‖ = |y i| := rfl
        rw [hyi]
        nlinarith [h i, abs_nonneg (y i)]
    _ = N := by simp

theorem solution {n N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (Cin : Matrix (Fin N) (Fin n) ℝ)
    (ζ : EuclideanSpace ℝ (Fin N)) (σ : ℝ → ℝ) (Lσ nA M : ℝ)
    (hσ : IsSquashing σ Lσ) (hnA : 0 ≤ nA)
    (hA : ∀ v : EuclideanSpace ℝ (Fin N),
      ‖(EuclideanSpace.equiv (Fin N) ℝ).symm (A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v))‖
        ≤ nA * ‖v‖)
    (hspec : nA * Lσ < 1) (hM : 0 < M) (hN : 0 < N)
    (z : ℕ → EuclideanSpace ℝ (Fin n)) (hz : UnifBdd M z) :
    ∃! x : ℕ → EuclideanSpace ℝ (Fin N),
      (∀ k i, x k i ∈ Set.Icc (-1 : ℝ) 1) ∧ IsESNSolution A Cin ζ σ z x := by
  set L := Real.sqrt N with hLdef
  set r := nA * Lσ with hrdef
  have hLpos : 0 < L := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hrangeAbs : ∀ (v : EuclideanSpace ℝ (Fin N)) (w : EuclideanSpace ℝ (Fin n)) i,
      |Fmap A Cin ζ σ v w i| ≤ 1 := by
    intro v w i
    rw [Fmap_apply]
    have := hσ.range_mem ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
      + Cin *ᵥ (EuclideanSpace.equiv (Fin n) ℝ w)) i + ζ i)
    exact abs_le.mpr ⟨this.1, this.2⟩
  have hmaps_to : ∀ (v : EuclideanSpace ℝ (Fin N)) (w : EuclideanSpace ℝ (Fin n)),
      ‖Fmap A Cin ζ σ v w‖ ≤ L :=
    fun v w => norm_le_sqrt_of_forall_abs_le _ (hrangeAbs v w)
  have hcontract : ∀ (v v' : EuclideanSpace ℝ (Fin N)) (w : EuclideanSpace ℝ (Fin n)),
      ‖Fmap A Cin ζ σ v w - Fmap A Cin ζ σ v' w‖ ≤ r * ‖v - v'‖ := by
    intro v v' w
    have hAdiff : A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
        - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')
        = A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ (v - v')) := by
      rw [map_sub, Matrix.mulVec_sub]
    have hAnorm : ‖(EuclideanSpace.equiv (Fin N) ℝ).symm
        (A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
          - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v'))‖ ≤ nA * ‖v - v'‖ := by
      rw [hAdiff]; exact hA (v - v')
    have hsq : ‖Fmap A Cin ζ σ v w - Fmap A Cin ζ σ v' w‖ ^ 2 ≤ (r * ‖v - v'‖) ^ 2 := by
      have hL0 : (0:ℝ) ≤ Lσ := hσ.lipschitz_nonneg
      have hnorm_sq : ‖Fmap A Cin ζ σ v w - Fmap A Cin ζ σ v' w‖ ^ 2
          = ∑ i, (Fmap A Cin ζ σ v w i - Fmap A Cin ζ σ v' w i) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        congr 1
        funext i
        have : (Fmap A Cin ζ σ v w - Fmap A Cin ζ σ v' w) i
            = Fmap A Cin ζ σ v w i - Fmap A Cin ζ σ v' w i := rfl
        rw [this]
        have hnormeq : ‖Fmap A Cin ζ σ v w i - Fmap A Cin ζ σ v' w i‖
            = |Fmap A Cin ζ σ v w i - Fmap A Cin ζ σ v' w i| := rfl
        rw [hnormeq, sq_abs]
      have hterm : ∀ i, (Fmap A Cin ζ σ v w i - Fmap A Cin ζ σ v' w i) ^ 2
          ≤ (Lσ * ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
              - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')) i)) ^ 2 := by
        intro i
        rw [Fmap_apply, Fmap_apply]
        have hlip := hσ.lipschitz ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
            + Cin *ᵥ (EuclideanSpace.equiv (Fin n) ℝ w)) i + ζ i)
          ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')
            + Cin *ᵥ (EuclideanSpace.equiv (Fin n) ℝ w)) i + ζ i)
        have heq : ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
              + Cin *ᵥ (EuclideanSpace.equiv (Fin n) ℝ w)) i + ζ i)
            - ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')
              + Cin *ᵥ (EuclideanSpace.equiv (Fin n) ℝ w)) i + ζ i)
            = (A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
                - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')) i := by
          simp [Pi.add_apply, Pi.sub_apply]
        rw [heq] at hlip
        have habs : |σ ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
              + Cin *ᵥ (EuclideanSpace.equiv (Fin n) ℝ w)) i + ζ i)
            - σ ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')
              + Cin *ᵥ (EuclideanSpace.equiv (Fin n) ℝ w)) i + ζ i)|
            ≤ Lσ * |(A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
                - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')) i| := hlip
        have h1 : (σ ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
              + Cin *ᵥ (EuclideanSpace.equiv (Fin n) ℝ w)) i + ζ i)
            - σ ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')
              + Cin *ᵥ (EuclideanSpace.equiv (Fin n) ℝ w)) i + ζ i)) ^ 2
            ≤ (Lσ * |(A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
                - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')) i|) ^ 2 :=
          sq_le_sq' (by linarith [abs_le.mp habs |>.1]) (by linarith [abs_le.mp habs |>.2])
        calc (σ ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
                + Cin *ᵥ (EuclideanSpace.equiv (Fin n) ℝ w)) i + ζ i)
              - σ ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')
                + Cin *ᵥ (EuclideanSpace.equiv (Fin n) ℝ w)) i + ζ i)) ^ 2
            ≤ (Lσ * |(A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
                - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')) i|) ^ 2 := h1
          _ = (Lσ * ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
                - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')) i)) ^ 2 := by
              rw [mul_pow, mul_pow, sq_abs]
      have hsum : ∑ i, (Fmap A Cin ζ σ v w i - Fmap A Cin ζ σ v' w i) ^ 2
          ≤ ∑ i, (Lσ * ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
              - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')) i)) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hterm i)
      have hsum2 : ∑ i, (Lσ * ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
            - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')) i)) ^ 2
          = Lσ ^ 2 * ‖(EuclideanSpace.equiv (Fin N) ℝ).symm
              (A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
                - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v'))‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
        congr 1
        funext i
        have heq2 : ((EuclideanSpace.equiv (Fin N) ℝ).symm
            (A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
              - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v'))) i
            = (A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
                - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')) i := rfl
        rw [heq2]
        have hnormeq2 : ‖(A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
              - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')) i‖
            = |(A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
                - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')) i| := rfl
        rw [mul_pow, hnormeq2, sq_abs]
      have hfinal : Lσ ^ 2 * ‖(EuclideanSpace.equiv (Fin N) ℝ).symm
              (A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
                - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v'))‖ ^ 2
          ≤ Lσ ^ 2 * (nA * ‖v - v'‖) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg Lσ)
        apply sq_le_sq' _ hAnorm
        have := norm_nonneg ((EuclideanSpace.equiv (Fin N) ℝ).symm
            (A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
              - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')))
        nlinarith [hAnorm, mul_nonneg hnA (norm_nonneg (v - v'))]
      rw [hnorm_sq]
      calc ∑ i, (Fmap A Cin ζ σ v w i - Fmap A Cin ζ σ v' w i) ^ 2
          ≤ ∑ i, (Lσ * ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
              - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v')) i)) ^ 2 := hsum
        _ = Lσ ^ 2 * ‖(EuclideanSpace.equiv (Fin N) ℝ).symm
              (A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v)
                - A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ v'))‖ ^ 2 := hsum2
        _ ≤ Lσ ^ 2 * (nA * ‖v - v'‖) ^ 2 := hfinal
        _ = (r * ‖v - v'‖) ^ 2 := by rw [hrdef]; ring
    have hLσ0 : 0 ≤ Lσ := hσ.lipschitz_nonneg
    have hX0 : 0 ≤ ‖Fmap A Cin ζ σ v w - Fmap A Cin ζ σ v' w‖ := norm_nonneg _
    have hY0 : 0 ≤ r * ‖v - v'‖ :=
      mul_nonneg (by rw [hrdef]; exact mul_nonneg hnA hLσ0) (norm_nonneg _)
    nlinarith [hsq, hX0, hY0]
  have hLσ0 : 0 ≤ Lσ := hσ.lipschitz_nonneg
  have hF : IsContracting (Fmap A Cin ζ σ) L M r := by
    refine ⟨?_, ?_, hLpos, hM, ?_, ?_⟩
    · rw [hrdef]; exact mul_nonneg hnA hLσ0
    · rw [hrdef]; exact hspec
    · intro v w _ _; exact hmaps_to v w
    · intro v v' w _ _ _; exact hcontract v v' w
  obtain ⟨xabs, ⟨hxabs_bdd, hxabs_sol⟩, hxabs_uniq⟩ :=
    ReservoirESN.esp_of_contracting (Fmap A Cin ζ σ) L M r hF z hz
  refine ⟨xabs, ⟨?_, ?_⟩, ?_⟩
  · intro k i
    have hesn : IsESNSolution A Cin ζ σ z xabs :=
      (isSolution_iff_isESNSolution A Cin ζ σ z xabs).mp hxabs_sol
    rw [hesn k i]
    exact hσ.range_mem _
  · exact (isSolution_iff_isESNSolution A Cin ζ σ z xabs).mp hxabs_sol
  · rintro y ⟨hy_range, hy_sol⟩
    apply hxabs_uniq
    refine ⟨?_, (isSolution_iff_isESNSolution A Cin ζ σ z y).mpr hy_sol⟩
    intro k
    apply norm_le_sqrt_of_forall_abs_le
    intro i
    exact abs_le.mpr ⟨(hy_range k i).1, (hy_range k i).2⟩
