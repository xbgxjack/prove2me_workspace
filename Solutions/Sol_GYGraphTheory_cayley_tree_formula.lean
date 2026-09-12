import Theorems.Thm_GYGraphTheory_prop_3_7_3
import Theorems.Thm_GYGraphTheory_prop_3_7_4
import Mathlib

open scoped Classical

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {T : SimpleGraph (Fin n) // T.IsTree} = n ^ (n - 2) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨hdec_enc, henc_dec⟩ := GYGraphTheory.prop_3_7_4 hn
  have hbij : Function.Bijective
      (fun T : {T : SimpleGraph (Fin n) // T.IsTree} => GYGraphTheory.pruferEncode T.1) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun s => ⟨GYGraphTheory.pruferDecode s, GYGraphTheory.prop_3_7_3 hn s⟩, ?_, ?_⟩
    · intro T
      exact Subtype.ext (hdec_enc T.1 T.2)
    · intro s
      exact henc_dec s
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_fun, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin]
