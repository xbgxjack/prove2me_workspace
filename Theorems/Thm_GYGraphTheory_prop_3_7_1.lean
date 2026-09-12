import Definitions.Def_GYGraphTheory
import Mathlib

open scoped Classical

namespace GYGraphTheory
theorem prop_3_7_1 {n : ℕ} (hn : 2 ≤ n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) (k : Fin n) :
    haveI : NeZero n := ⟨by omega⟩
    T.degree k = (List.ofFn (pruferEncode T)).count k + 1 := by sorry
end GYGraphTheory
