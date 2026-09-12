import Definitions.Def_GYGraphTheory
import Mathlib

open scoped Classical

namespace GYGraphTheory
theorem corollary_3_7_2 {n : ℕ} (hn : 2 ≤ n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) (k : Fin n) :
    haveI : NeZero n := ⟨by omega⟩
    k ∈ List.ofFn (pruferEncode T) ↔ T.degree k ≠ 1 := by sorry
end GYGraphTheory
