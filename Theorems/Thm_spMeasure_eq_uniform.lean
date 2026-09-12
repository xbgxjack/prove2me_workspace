import Definitions.Def_Komlos_RandomSignModel
import Mathlib
open Komlos MeasureTheory

theorem spMeasure_eq_uniform (n : ℕ) :
    spMeasure n = (PMF.uniformOfFintype (SpOmega n)).toMeasure := by sorry
