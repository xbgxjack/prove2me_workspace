import Mathlib
open MeasureTheory Filter Topology Polynomial
open scoped ENNReal NNReal

theorem solution (n : ℕ) (hn : 1 ≤ n) (a : ℕ → ℂ) (han : a n ≠ 0) :
    ∃ z : ℂ, ∑ k ∈ Finset.range (n + 1), a k * z ^ k = 0 := by
  set p : ℂ[X] := ∑ k ∈ Finset.range (n + 1), C (a k) * X ^ k with hp
  have hdeg_le : p.degree ≤ (n : WithBot ℕ) := by
    rw [hp]
    refine le_trans (degree_sum_le _ _) ?_
    simp only [Finset.sup_le_iff, Finset.mem_range]
    intro k hk
    calc (C (a k) * X ^ k).degree ≤ (C (a k)).degree + (X ^ k : ℂ[X]).degree :=
          degree_mul_le _ _
      _ ≤ 0 + (k : WithBot ℕ) := add_le_add degree_C_le (degree_X_pow_le k)
      _ = (k : WithBot ℕ) := by simp
      _ ≤ (n : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_iff.mp hk
  have hcoeff : p.coeff n = a n := by
    rw [hp, finsetSum_coeff]
    rw [Finset.sum_eq_single n]
    · simp
    · intro k _ hkn
      have hnk : (n : ℕ) ≠ k := fun h => hkn h.symm
      simp [coeff_C_mul, coeff_X_pow, hnk]
    · intro h
      exact absurd (Finset.self_mem_range_succ n) h
  have hdeg : p.degree = (n : WithBot ℕ) :=
    degree_eq_of_le_of_coeff_ne_zero hdeg_le (by rw [hcoeff]; exact han)
  have hpos : 0 < p.degree := by
    rw [hdeg]; exact_mod_cast hn
  obtain ⟨z, hz⟩ := Complex.exists_root hpos
  refine ⟨z, ?_⟩
  have h2 := hz
  rw [IsRoot, hp, eval_finsetSum] at h2
  simpa using h2
