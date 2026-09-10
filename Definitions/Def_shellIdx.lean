import Mathlib
import Definitions.Def_rowSumB

noncomputable def shellIdx {m : ℕ} (Δ : ℝ) (a : Fin m → ℝ) (ω : Fin m → Bool) : ℤ :=
  round (rowSumB a ω / (2*Δ))
