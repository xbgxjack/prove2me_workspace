import Mathlib

/-!
Hatcher, *Algebraic Topology*, Section 1.3 "Covering Spaces" (pp. 56–72).

Objects appearing in the classification of covering spaces and in the theory of deck
transformations: semilocal simple connectivity (p. 63), the induced homomorphism
`p_* : π₁(X̃, x̃₀) → π₁(X, x₀)` and its image subgroup `H = p_*(π₁(X̃, x̃₀))` (p. 61),
covering spaces of `X` with and without basepoints and their isomorphisms (p. 67),
the deck transformation group `G(X̃)` and normal covering spaces (p. 70), and covering
space actions with their orbit spaces `Y/G` (p. 72).
-/

noncomputable section

namespace Hatcher

universe u

section SpaceProperties

variable (X : Type*) [TopologicalSpace X]

/-- Hatcher, p. 63: `X` is **semilocally simply-connected** if each point `x ∈ X` has a
neighborhood `U` such that the inclusion-induced map `π₁(U, x) → π₁(X, x)` is trivial, i.e.
every loop at `x` contained in `U` is null-homotopic in `X`. -/
def IsSemilocallySimplyConnected : Prop :=
  ∀ x : X, ∃ U ∈ nhds x, ∀ γ : Path x x, (∀ t, γ t ∈ U) → γ.Homotopic (Path.refl x)

end SpaceProperties

section CoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] (p : E → X)

/-- `p_* : π₁(X̃, x̃₀) → π₁(X, x₀)`, the homomorphism induced by a covering space
`p : (X̃, x̃₀) → (X, x₀)` (Hatcher, p. 61). -/
def coverHom (hp : Continuous p) {e₀ : E} {x₀ : X} (he : p e₀ = x₀) :
    FundamentalGroup E e₀ →* FundamentalGroup X x₀ :=
  FundamentalGroup.mapOfEq ⟨p, hp⟩ he

/-- The image subgroup `H = p_*(π₁(X̃, x̃₀)) ⊆ π₁(X, x₀)` of a covering space
`p : (X̃, x̃₀) → (X, x₀)` (Hatcher, p. 61). -/
def coverSubgroup (hp : Continuous p) {e₀ : E} {x₀ : X} (he : p e₀ = x₀) :
    Subgroup (FundamentalGroup X x₀) :=
  (coverHom p hp he).range

/-- The group `G(X̃)` of **deck transformations** of `p : X̃ → X` (Hatcher, p. 70): the
homeomorphisms `f : X̃ → X̃` with `p ∘ f = p`, a subgroup of the group of all
self-homeomorphisms of `X̃` under composition. -/
def deckGroup : Subgroup (E ≃ₜ E) where
  carrier := {f | ∀ e, p (f e) = p e}
  mul_mem' {f g} hf hg e := by
    change p (f (g e)) = p e
    rw [hf, hg]
  one_mem' _ := rfl
  inv_mem' {f} hf e := by
    change p (f.symm e) = p e
    rw [← hf (f.symm e), f.apply_symm_apply]

/-- `p : X̃ → X` is a **normal** covering space (Hatcher, p. 70): for each `x ∈ X` and each
pair of lifts `x̃, x̃'` of `x` there is a deck transformation taking `x̃` to `x̃'`. -/
def IsNormalCover : Prop :=
  ∀ e e' : E, p e = p e' → ∃ f ∈ deckGroup p, f e = e'

end CoveringMap

section Classification

variable (X : Type u) [TopologicalSpace X]

/-- A **covering space** of `X` (Hatcher, p. 56): a space `X̃` together with a covering map
`p : X̃ → X`. -/
structure CoveringSpace where
  /-- The total space `X̃`. -/
  E : Type u
  [topE : TopologicalSpace E]
  /-- The covering map `p : X̃ → X`. -/
  p : E → X
  isCoveringMap : IsCoveringMap p

attribute [instance] CoveringSpace.topE

/-- A covering space `p : (X̃, x̃₀) → (X, x₀)` with a chosen basepoint `x̃₀ ∈ p⁻¹(x₀)`
(Hatcher, p. 61). -/
structure PointedCover (x₀ : X) extends CoveringSpace X where
  /-- The basepoint `x̃₀ ∈ X̃`. -/
  e₀ : E
  p_e₀ : p e₀ = x₀

variable {X}

/-- Two covering spaces `p₁ : X̃₁ → X`, `p₂ : X̃₂ → X` are **isomorphic** (Hatcher, p. 67) if there
is a homeomorphism `f : X̃₁ → X̃₂` with `p₁ = p₂ ∘ f`. -/
def IsIsomorphic (C₁ C₂ : CoveringSpace X) : Prop :=
  ∃ f : C₁.E ≃ₜ C₂.E, ∀ e, C₂.p (f e) = C₁.p e

/-- The subgroup `p_*(π₁(X̃, x̃₀)) ⊆ π₁(X, x₀)` associated to a covering space with basepoint
(Hatcher, Theorem 1.38, p. 67). -/
def PointedCover.subgroup {x₀ : X} (C : PointedCover X x₀) : Subgroup (FundamentalGroup X x₀) :=
  coverSubgroup C.p C.isCoveringMap.continuous C.p_e₀

/-- Two covering spaces with basepoints are **isomorphic preserving basepoints** (Hatcher,
Proposition 1.37, p. 67): there is an isomorphism `f : X̃₁ → X̃₂` of covering spaces
taking `x̃₁` to `x̃₂`. -/
def IsPointedIsomorphic {x₀ : X} (C₁ C₂ : PointedCover X x₀) : Prop :=
  ∃ f : C₁.E ≃ₜ C₂.E, (∀ e, C₂.p (f e) = C₁.p e) ∧ f C₁.e₀ = C₂.e₀

end Classification

section GroupActions

variable (G : Type*) [Group G] (Y : Type*) [TopologicalSpace Y] [MulAction G Y]

/-- Hatcher's condition `(∗)` (p. 72): an action of `G` on `Y` by homeomorphisms is a
**covering space action** if each `y ∈ Y` has a neighborhood `U` such that the images `g(U)`,
`g ∈ G`, are pairwise disjoint; equivalently, `U ∩ g(U) ≠ ∅` only for `g = 1`. -/
def IsCoveringSpaceAction : Prop :=
  (∀ g : G, Continuous fun y : Y => g • y) ∧
    ∀ y : Y, ∃ U ∈ nhds y, ∀ g : G, ((fun z => g • z) '' U ∩ U).Nonempty → g = 1

/-- The **orbit space** `Y/G` (Hatcher, p. 72): the quotient of `Y` identifying each `y` with
all its images `g(y)`, `g ∈ G`, with the quotient topology. -/
abbrev OrbitSpace : Type _ := MulAction.orbitRel.Quotient G Y

/-- The quotient map `p : Y → Y/G`, `p(y) = Gy` (Hatcher, Proposition 1.40, p. 72). -/
def orbitProj : Y → OrbitSpace G Y := Quotient.mk _

theorem continuous_orbitProj : Continuous (orbitProj G Y) := continuous_quotient_mk'

end GroupActions

end Hatcher

end

