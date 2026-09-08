import Definitions.Def_Hatcher_Covering
import Mathlib

open Hatcher unitInterval

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} (cov : IsCoveringMap p) {e₀ : E} {x₀ : X} (he : p e₀ = x₀)

/-- A representative loop `γ` (i.e. its class `⟦γ⟧`) has monodromy fixing `e₀` iff `γ` itself
lifts to a loop `Γ` based at `e₀`. -/
private theorem monodromy_eq_iff_exists_lift (γ : Path x₀ x₀) :
    (cov.monodromy (Path.Homotopic.Quotient.mk γ) ⟨e₀, he⟩ : E) = e₀ ↔
      ∃ Γ : Path e₀ e₀, ∀ t, p (Γ t) = γ t := by
  have hγ0 : γ 0 = p e₀ := γ.source.trans he.symm
  rw [show (cov.monodromy (Path.Homotopic.Quotient.mk γ) ⟨e₀, he⟩ : E)
      = cov.liftPath γ.toContinuousMap e₀ hγ0 1 from rfl]
  constructor
  · intro heq
    exact ⟨⟨cov.liftPath γ.toContinuousMap e₀ hγ0, cov.liftPath_zero .., heq⟩,
      fun t => congr_fun (cov.liftPath_lifts γ.toContinuousMap e₀ hγ0) t⟩
  · rintro ⟨Γ, hΓ⟩
    have hcont : Γ.toContinuousMap = cov.liftPath γ.toContinuousMap e₀ hγ0 :=
      (cov.eq_liftPath_iff' hγ0).mpr ⟨funext hΓ, Γ.source⟩
    have h1 : Γ 1 = cov.liftPath γ.toContinuousMap e₀ hγ0 1 :=
      congrFun (congrArg (fun f : C(I, E) => (f : I → E)) hcont) 1
    rw [← h1]
    exact Γ.target

/-- `g` lies in the image subgroup of `p_*` iff monodromy along `g` fixes `e₀`. -/
private theorem key (g : FundamentalGroup X x₀) :
    g ∈ Hatcher.coverSubgroup p cov.continuous he ↔
      (cov.monodromy g ⟨e₀, he⟩ : E) = e₀ := by
  show g ∈ (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he).range ↔ _
  constructor
  · rintro ⟨h, rfl⟩
    induction h using Path.Homotopic.Quotient.ind with
    | mk δ =>
      have hval : FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he
          (Path.Homotopic.Quotient.mk δ) =
          Path.Homotopic.Quotient.mk ((δ.map cov.continuous).cast he.symm he.symm) := by
        rw [FundamentalGroup.mapOfEq_apply]; rfl
      rw [hval, monodromy_eq_iff_exists_lift cov he]
      exact ⟨δ, fun t => rfl⟩
  · intro heq
    induction g using Path.Homotopic.Quotient.ind with
    | mk γ =>
      obtain ⟨Γ, hΓ⟩ := (monodromy_eq_iff_exists_lift cov he γ).mp heq
      refine ⟨Path.Homotopic.Quotient.mk Γ, ?_⟩
      have hval : FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he
          (Path.Homotopic.Quotient.mk Γ) =
          Path.Homotopic.Quotient.mk ((Γ.map cov.continuous).cast he.symm he.symm) := by
        rw [FundamentalGroup.mapOfEq_apply]; rfl
      rw [hval]
      exact congrArg Path.Homotopic.Quotient.mk (Path.ext (funext hΓ))

theorem mem_coverSubgroup_iff (g : FundamentalGroup X x₀) :
    g ∈ Hatcher.coverSubgroup p cov.continuous he ↔
      ∀ γ : Path x₀ x₀, FundamentalGroup.fromPath ⟦γ⟧ = g →
        ∃ Γ : Path e₀ e₀, ∀ t, p (Γ t) = γ t := by
  rw [key cov he]
  constructor
  · intro heq γ hγ
    have hgγ : (Path.Homotopic.Quotient.mk γ : FundamentalGroup X x₀) = g := hγ
    exact (monodromy_eq_iff_exists_lift cov he γ).mp (hgγ ▸ heq)
  · intro hall
    induction g using Path.Homotopic.Quotient.ind with
    | mk γ =>
      exact (monodromy_eq_iff_exists_lift cov he γ).mpr (hall γ rfl)

theorem solution {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) {e₀ : E} {x₀ : X} (he : p e₀ = x₀)
    (g : FundamentalGroup X x₀) :
    g ∈ Hatcher.coverSubgroup p hp.continuous he ↔
      ∀ γ : Path x₀ x₀, FundamentalGroup.fromPath ⟦γ⟧ = g →
        ∃ Γ : Path e₀ e₀, ∀ t, p (Γ t) = γ t :=
  mem_coverSubgroup_iff hp he g
