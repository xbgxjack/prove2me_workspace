import Definitions.Def_Komlos_RandomSignModel
import Theorems.Thm_spMeasure_eq_uniform
import Mathlib
open Komlos MeasureTheory

theorem spMeasure_real_coe_finset (n : ℕ) (S : Finset (SpOmega n)) :
    (spMeasure n).real (S : Set (SpOmega n)) = (S.card : ℝ) / (2 : ℝ) ^ n := by sorry
