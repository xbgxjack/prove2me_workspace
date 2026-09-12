import Definitions.Def_DiscreteEntropy
import Mathlib

open Finset

variable {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] [Nonempty Ω]

theorem shannonEntropy_pigeonhole (Z : Ω → β) [Nonempty β] :
    ∃ b : β, (Fintype.card Ω : ℝ) * (2:ℝ) ^ (-shannonEntropy Z)
        ≤ ((univ.filter (fun ω => Z ω = b)).card : ℝ) := by sorry
