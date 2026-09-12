import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert
import Definitions.Def_ErdosStraus242

namespace ErdosStraus242

theorem mordell_840 (p : ℕ) (hp : Nat.Prime p) (hp2 : 2 < p)
    (hres : p % 840 ∉ ({1, 121, 169, 289, 361, 529} : Finset ℕ)) :
    IsErdosStraus p := by
  sorry

end ErdosStraus242
