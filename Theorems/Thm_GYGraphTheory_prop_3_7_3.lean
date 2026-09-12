import Definitions.Def_GYGraphTheory
import Mathlib

namespace GYGraphTheory
theorem prop_3_7_3 {n : ℕ} (hn : 2 ≤ n) (s : Fin (n - 2) → Fin n) :
    haveI : NeZero n := ⟨by omega⟩
    (pruferDecode s).IsTree := by sorry
end GYGraphTheory
