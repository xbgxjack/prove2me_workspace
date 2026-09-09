import Definitions.Def_DiscreteEntropy
import Theorems.Thm_gibbs_inequality
import Mathlib

open Finset

variable {Ω β1 β2 : Type*} [Fintype Ω] [Fintype β1] [Fintype β2]
  [DecidableEq β1] [DecidableEq β2] [Nonempty Ω]

theorem shannonEntropy_prod_le (Z1 : Ω → β1) (Z2 : Ω → β2) :
    shannonEntropy (fun ω => (Z1 ω, Z2 ω)) ≤ shannonEntropy Z1 + shannonEntropy Z2 := by sorry
