import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_ErdosStraus242

namespace ErdosStraus242

theorem mod24_reduction :
    (∀ n : ℕ, 2 < n → IsErdosStraus n) ↔
    (∀ p : ℕ, Nat.Prime p → p % 24 = 1 → IsErdosStraus p) := by
  sorry

end ErdosStraus242
