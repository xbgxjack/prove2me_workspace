import Theorems.Thm_GYGraphTheory_prop_3_7_1
import Mathlib

open scoped Classical

theorem solution {n : ℕ} (hn : 2 ≤ n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) (k : Fin n) :
    haveI : NeZero n := ⟨by omega⟩
    k ∈ List.ofFn (GYGraphTheory.pruferEncode T) ↔ T.degree k ≠ 1 := by
  haveI : NeZero n := ⟨by omega⟩
  rw [GYGraphTheory.prop_3_7_1 hn T hT k]
  rw [← List.count_pos_iff]
  omega
