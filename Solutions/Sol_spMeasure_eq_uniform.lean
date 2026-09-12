import Definitions.Def_Komlos_RandomSignModel
import Mathlib
open Komlos MeasureTheory

theorem solution (n : ℕ) :
    spMeasure n = (PMF.uniformOfFintype (SpOmega n)).toMeasure := by
  apply MeasureTheory.Measure.ext_of_singleton
  intro ω
  rw [spMeasure, Measure.pi_singleton]
  have h1 : ∀ i, (PMF.uniformOfFintype Bool).toMeasure {ω i} = (2 : ENNReal)⁻¹ := by
    intro i
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply]
    norm_num
  simp_rw [h1]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply]
  rw [Fintype.card_fun]
  simp only [Fintype.card_bool, Fintype.card_fin]
  push_cast
  exact ENNReal.inv_pow.symm
