import Definitions.Def_GYGraphTheory
import Mathlib

namespace GYGraphTheory
theorem prop_3_7_4 {n : ℕ} (hn : 2 ≤ n) :
    haveI : NeZero n := ⟨by omega⟩
    (∀ T : SimpleGraph (Fin n), T.IsTree → pruferDecode (pruferEncode T) = T) ∧
      (∀ s : Fin (n - 2) → Fin n, pruferEncode (pruferDecode s) = s) := by sorry
end GYGraphTheory
