import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Definitions.Def_SelectedClass
open scoped EuclideanGeometry Real
open Batch3N9
open Problem97

theorem solution {A : Finset (EuclideanSpace ℝ (Fin 2))} {s : EuclideanSpace ℝ (Fin 2)} {d : ℝ} {q : EuclideanSpace ℝ (Fin 2)} :
    q ∈ Batch3N9.Problem97.SelectedClass A s d ↔ q ∈ A ∧ dist s q = d := by
  simp [Batch3N9.Problem97.SelectedClass]
