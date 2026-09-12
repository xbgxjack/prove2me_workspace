import Mathlib.Data.Rat.Cast.Order

namespace ErdosStraus242

/-- The exact distinct-denominator property, with rational division. -/
def IsErdosStraus (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
    (4 / n : ℚ) = 1 / x + 1 / y + 1 / z

end ErdosStraus242
