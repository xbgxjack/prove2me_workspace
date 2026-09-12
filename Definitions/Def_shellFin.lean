import Mathlib
import Definitions.Def_shellIdx

noncomputable def shellFin {m : ℕ} (Δ : ℝ) (a : Fin m → ℝ) (ω : Fin m → Bool) : Fin (2*m+3) :=
  ⟨(shellIdx Δ a ω + (m+1)).toNat % (2*m+3), Nat.mod_lt _ (by omega)⟩
