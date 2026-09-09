import Mathlib

open Finset

/-- A family of subsets of `Fin n` is `t`-intersecting if every pair of members
(including a set intersected with itself) has intersection size at least `t`. -/
def TIntersecting {n : ℕ} (t : ℕ) (𝒜 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, t ≤ (A ∩ B).card

/-- Katona's target bound `M(n,t)` for the even case `2 ∣ (n+t)`. -/
noncomputable def katonaBound (n t : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc ((n + t) / 2) n, n.choose i

-- Base case t = 1: a 1-intersecting family is exactly a `Set.Intersecting` family
-- (pairwise not disjoint, including self), so Mathlib's `Intersecting.card_le` applies.
example {n : ℕ} (𝒜 : Finset (Finset (Fin n))) (h : TIntersecting 1 𝒜) :
    2 * 𝒜.card ≤ 2 ^ n := by
  have hint : (𝒜 : Set (Finset (Fin n))).Intersecting := by
    intro A hA B hB hdisj
    have := h A hA B hB
    rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
    simp [hdisj] at this
  have := hint.card_le (α := Finset (Fin n))
  simpa using this
