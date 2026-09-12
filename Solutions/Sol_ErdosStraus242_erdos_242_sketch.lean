import Mathlib
import Definitions.Def_ErdosStraus242
import Theorems.Thm_ErdosStraus242_mod24_reduction
import Theorems.Thm_ErdosStraus242_mordell_840
import Theorems.Thm_ErdosStraus242_hard_core_840

open ErdosStraus242

theorem solution : ∀ n : ℕ, 2 < n → IsErdosStraus n := by
  rw [mod24_reduction]
  intro p hp hp24
  have hp2 : 2 < p := by have := hp.two_le; omega
  by_cases hres : p % 840 ∈ ({1, 121, 169, 289, 361, 529} : Finset ℕ)
  · exact hard_core_840 p hp hp2 hres
  · exact mordell_840 p hp hp2 hres
