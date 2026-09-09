import Mathlib

namespace Katona

/-- A family of subsets of a finite type is `t`-intersecting if every pair of members
(including a set intersected with itself) has intersection size at least `t`. -/
def TIntersecting {α : Type*} [DecidableEq α] (t : ℕ) (𝒜 : Finset (Finset α)) : Prop :=
  ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, t ≤ (A ∩ B).card

end Katona
