import Definitions.Def_GYGraphTheory
import Mathlib

namespace GYGraphTheory
theorem cayley_tree_formula (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {T : SimpleGraph (Fin n) // T.IsTree} = n ^ (n - 2) := by sorry
end GYGraphTheory
