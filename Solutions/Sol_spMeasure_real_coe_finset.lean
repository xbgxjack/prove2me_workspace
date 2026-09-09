import Definitions.Def_Komlos_RandomSignModel
import Theorems.Thm_spMeasure_eq_uniform
import Mathlib
open Komlos MeasureTheory

theorem solution (n : ℕ) (S : Finset (SpOmega n)) :
    (spMeasure n).real (S : Set (SpOmega n)) = (S.card : ℝ) / (2 : ℝ) ^ n := by
  rw [Measure.real, spMeasure_eq_uniform, PMF.toMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : Fintype.card (SpOmega n) = 2 ^ n := by rw [Fintype.card_fun]; simp
  rw [hcard, ENNReal.toReal_mul]
  push_cast
  rw [ENNReal.toReal_inv]
  simp [div_eq_mul_inv]
