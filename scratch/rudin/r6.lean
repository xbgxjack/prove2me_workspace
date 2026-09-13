import Mathlib
open Filter Topology Set

-- ch07_interchange_limits
example {X : Type*} [MetricSpace X] (E : Set X) (f : ℕ → X → ℂ)
    (g : X → ℂ) (A : ℕ → ℂ) (x : X) (hx : x ∈ closure (E \ {x}))
    (huc : TendstoUniformlyOn f g atTop E)
    (hA : ∀ n, Tendsto (f n) (𝓝[E \ {x}] x) (𝓝 (A n))) :
    ∃ L : ℂ, Tendsto A atTop (𝓝 L) ∧ Tendsto g (𝓝[E \ {x}] x) (𝓝 L) := by
  have hne : (𝓝[E \ {x}] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hx
  -- the sequence A is Cauchy
  have hcau : CauchySeq A := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hucs := huc.uniformCauchySeqOn
    rw [Metric.uniformCauchySeqOn_iff] at hucs
    obtain ⟨N, hN⟩ := hucs (ε / 2) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hlim : Tendsto (fun y => dist (f m y) (f n y)) (𝓝[E \ {x}] x) (𝓝 (dist (A m) (A n))) :=
      (hA m).dist (hA n)
    have hbd : ∀ᶠ y in 𝓝[E \ {x}] x, dist (f m y) (f n y) ≤ ε / 2 := by
      have hmem : ∀ᶠ y in 𝓝[E \ {x}] x, y ∈ E := by
        filter_upwards [self_mem_nhdsWithin] with y hy using hy.1
      filter_upwards [hmem] with y hy using (hN m hm n hn y hy).le
    have : dist (A m) (A n) ≤ ε / 2 := le_of_tendsto hlim hbd
    linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨L, hL, ?_⟩
  have hmono : 𝓝[E \ {x}] x ≤ 𝓟 E :=
    le_trans inf_le_right (principal_mono.mpr Set.sdiff_subset)
  exact (huc.tendstoUniformlyOnFilter.mono_right hmono).tendsto_of_eventually_tendsto
    (Eventually.of_forall hA) hL
