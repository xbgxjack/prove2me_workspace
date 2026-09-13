import Mathlib
open Filter Topology Set

theorem solution (n : ℕ)
    (inv : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hinv : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      Function.Bijective A → (∀ x, inv A (A x) = x) ∧ ∀ y, A (inv A y) = y) :
    (∀ A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        Function.Bijective A → ‖B - A‖ * ‖inv A‖ < 1 → Function.Bijective B) ∧
    IsOpen {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) | Function.Bijective A} ∧
    ContinuousOn inv {A | Function.Bijective A} := by
  set E := EuclideanSpace ℝ (Fin n)
  -- (1) perturbation
  have part1 : ∀ A B : E →L[ℝ] E, Function.Bijective A → ‖B - A‖ * ‖inv A‖ < 1 →
      Function.Bijective B := by
    intro A B hA hlt
    obtain ⟨hl, _⟩ := hinv A hA
    have hkey : ∀ x : E, (1 - ‖inv A‖ * ‖B - A‖) * ‖x‖ ≤ ‖inv A‖ * ‖B x‖ := by
      intro x
      have h1 : ‖x‖ ≤ ‖inv A‖ * ‖A x‖ := by
        calc ‖x‖ = ‖inv A (A x)‖ := by rw [hl x]
          _ ≤ ‖inv A‖ * ‖A x‖ := (inv A).le_opNorm _
      have h2 : ‖A x‖ ≤ ‖B x‖ + ‖B - A‖ * ‖x‖ := by
        have : ‖A x - B x‖ ≤ ‖B - A‖ * ‖x‖ := by
          have hx : A x - B x = -((B - A) x) := by simp
          rw [hx, norm_neg]
          exact (B - A).le_opNorm _
        have := norm_le_norm_add_norm_sub' (A x) (B x)
        linarith [norm_sub_rev (A x) (B x), this]
      have hb : (0:ℝ) ≤ ‖inv A‖ := norm_nonneg _
      nlinarith [h1, h2, hb, norm_nonneg x]
    have hpos : 0 < 1 - ‖inv A‖ * ‖B - A‖ := by
      have := hlt; nlinarith [hlt]
    have hinj : Function.Injective B := by
      intro p q hpq
      have hz : B (p - q) = 0 := by rw [map_sub, hpq, sub_self]
      have h := hkey (p - q)
      rw [hz] at h
      simp only [norm_zero, mul_zero] at h
      have hle : ‖p - q‖ ≤ 0 := by nlinarith [norm_nonneg (p - q)]
      have hzz : p - q = 0 := norm_eq_zero.mp (le_antisymm hle (norm_nonneg (p - q)))
      exact sub_eq_zero.mp hzz
    exact ⟨hinj, by
      have : Function.Surjective (B : E →ₗ[ℝ] E) :=
        LinearMap.injective_iff_surjective.mp hinj
      exact this⟩
  refine ⟨part1, ?_, ?_⟩
  · -- (2) openness
    rw [Metric.isOpen_iff]
    intro A hA
    refine ⟨1 / (‖inv A‖ + 1), by positivity, ?_⟩
    intro B hB
    rw [Metric.mem_ball, dist_eq_norm] at hB
    refine part1 A B hA ?_
    have hb : (0:ℝ) ≤ ‖inv A‖ := norm_nonneg _
    have h1 : ‖B - A‖ < 1 / (‖inv A‖ + 1) := hB
    have h2 : (0:ℝ) < ‖inv A‖ + 1 := by linarith
    rw [lt_div_iff₀ h2] at h1
    nlinarith [norm_nonneg (B - A)]
  · -- (3) continuity of the inverse
    intro A hA
    have hA' : Function.Bijective A := hA
    obtain ⟨hl, hr⟩ := hinv A hA'
    have hmul1 : A * inv A = 1 := by
      apply ContinuousLinearMap.ext; intro y
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]; exact hr y
    have hmul2 : inv A * A = 1 := by
      apply ContinuousLinearMap.ext; intro y
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]; exact hl y
    let u : (E →L[ℝ] E)ˣ := ⟨A, inv A, hmul1, hmul2⟩
    have hAu : (u : E →L[ℝ] E) = A := rfl
    have hcont : ContinuousAt Ring.inverse (A : E →L[ℝ] E) := by
      rw [← hAu]; exact NormedRing.inverse_continuousAt u
    have heq : Set.EqOn inv Ring.inverse {A : E →L[ℝ] E | Function.Bijective A} := by
      intro C hC
      obtain ⟨hl', hr'⟩ := hinv C hC
      have h1 : C * inv C = 1 := by
        apply ContinuousLinearMap.ext; intro y
        rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]; exact hr' y
      have h2 : inv C * C = 1 := by
        apply ContinuousLinearMap.ext; intro y
        rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]; exact hl' y
      let v : (E →L[ℝ] E)ˣ := ⟨C, inv C, h1, h2⟩
      have : Ring.inverse (v : E →L[ℝ] E) = (↑v⁻¹ : E →L[ℝ] E) := Ring.inverse_unit v
      simpa [v] using this.symm
    exact (hcont.continuousWithinAt.congr heq (heq hA)).congr (fun y hy => rfl) rfl
