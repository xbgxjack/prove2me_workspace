import Definitions.Def_DiscreteEntropy
import Theorems.Thm_shannonEntropy_prod_le
import Mathlib
open Finset

theorem shannonEntropy_pi_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {n : ℕ} {γ : Type*} [Fintype γ] [DecidableEq γ]
    (Z : Fin n → Ω → γ) :
    shannonEntropy (fun ω i => Z i ω) ≤ ∑ i, shannonEntropy (Z i) := by sorry
