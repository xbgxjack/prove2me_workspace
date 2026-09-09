import Mathlib

namespace Komlos

noncomputable section

/-- The finite sample space of `n` independent fair coin flips, one per coordinate. -/
abbrev SpOmega (n : ℕ) := Fin n → Bool

/-- The uniform (i.i.d. fair-coin) probability measure on `SpOmega n`. -/
def spMeasure (n : ℕ) : MeasureTheory.Measure (SpOmega n) :=
  MeasureTheory.Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)

instance (n : ℕ) : MeasureTheory.IsProbabilityMeasure (spMeasure n) := by
  unfold spMeasure; infer_instance

end

end Komlos
