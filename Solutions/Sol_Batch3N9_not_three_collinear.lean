import Definitions.Def_Erdos9796Counting_Foundation
open Problem97
open scoped EuclideanGeometry

private theorem not_wbtw {A : Finset ℝ²} (hA : ConvexIndep A)
    {x y z : ℝ²} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxy : Wbtw ℝ x y z) (hyx : y ≠ x) (hyz : y ≠ z) : False := by
  have hmem : y ∈ convexHull ℝ ({x, z} : Set ℝ²) := by
    rw [convexHull_pair]
    exact hxy.mem_segment
  have hsub : ({x, z} : Set ℝ²) ⊆ (A : Set ℝ²) \ {y} := by
    intro p hp
    have hp' : p = x ∨ p = z := by simpa using hp
    rcases hp' with hpx | hpz
    · refine ⟨?_, ?_⟩
      · simpa [hpx] using hx
      · intro hy'
        have hyx' : x = y := by simpa [hpx] using hy'
        exact hyx hyx'.symm
    · refine ⟨?_, ?_⟩
      · simpa [hpz] using hz
      · intro hy'
        have hyz' : z = y := by simpa [hpz] using hy'
        exact hyz hyz'.symm
  exact hA y (by exact_mod_cast hy) (convexHull_mono hsub hmem)

theorem solution {A : Finset ℝ²} (hA : ConvexIndep A) {x y z : ℝ²}
    (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcol : Collinear ℝ ({x, y, z} : Set ℝ²)) : False := by
  rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
  · exact not_wbtw hA hx hy hz hw hxy.symm hyz
  · exact not_wbtw hA hy hz hx hw hyz.symm hxz.symm
  · exact not_wbtw hA hz hx hy hw hxz hxy
