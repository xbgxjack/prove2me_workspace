import Definitions.Def_Hatcher_Covering
import Mathlib

open Hatcher unitInterval

namespace Hatcher
theorem mem_coverSubgroup_iff {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) {e₀ : E} {x₀ : X} (he : p e₀ = x₀)
    (g : FundamentalGroup X x₀) :
    g ∈ coverSubgroup p hp.continuous he ↔
      ∀ γ : Path x₀ x₀, FundamentalGroup.fromPath ⟦γ⟧ = g →
        ∃ Γ : Path e₀ e₀, ∀ t, p (Γ t) = γ t := by sorry
end Hatcher
