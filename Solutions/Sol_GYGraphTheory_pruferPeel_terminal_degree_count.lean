import Definitions.Def_GYGraphTheory
import Theorems.Thm_GYGraphTheory_prop_3_7_1
import Mathlib

open scoped Classical

namespace GYGraphTheory

variable {n : ℕ} [NeZero n]

lemma pruferPeel_succ' (T : SimpleGraph (Fin n)) (i : ℕ) :
    pruferPeel T (i + 1) =
      ((pruferPeel T i).1.erase (leastActiveLeaf T (pruferPeel T i).1),
        (pruferPeel T i).2 ++ [leastActiveLeafNeighbor T (pruferPeel T i).1]) := by
  simp [pruferPeel]

lemma pruferPeel_acc_length' (T : SimpleGraph (Fin n)) (i : ℕ) :
    (pruferPeel T i).2.length = i := by
  induction i with
  | zero => simp [pruferPeel]
  | succ i ih => simp [pruferPeel_succ', ih]

lemma pruferPeel_acc_prefix' (T : SimpleGraph (Fin n)) {i j : ℕ} (hij : i ≤ j) (idx : ℕ)
    (hidx : idx < i) :
    (pruferPeel T j).2.getD idx 0 = (pruferPeel T i).2.getD idx 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · have hij' : i ≤ j := Nat.lt_succ_iff.mp h
      simp only [pruferPeel_succ']
      rw [List.getD_append _ _ _ _ (by rw [pruferPeel_acc_length']; omega)]
      exact ih hij'
    · have : i = j + 1 := le_antisymm hij h
      subst this; rfl

lemma ofFn_pruferEncode_eq' (T : SimpleGraph (Fin n)) :
    List.ofFn (pruferEncode T) = (pruferPeel T (n - 2)).2 := by
  apply List.ext_getElem (by simp [pruferPeel_acc_length'])
  intro i h1 h2
  simp only [List.getElem_ofFn]
  have hi2 : i < n - 2 := by simpa using h1
  show (pruferPeel T (i + 1)).2.getD i 0 = (pruferPeel T (n - 2)).2[i]'h2
  rw [← List.getD_eq_getElem _ _ h2]
  exact (pruferPeel_acc_prefix' T (by omega) i (by omega)).symm

end GYGraphTheory

open GYGraphTheory

theorem solution {n : ℕ} (hn : 2 ≤ n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) (k : Fin n) :
    haveI : NeZero n := ⟨by omega⟩
    T.degree k = (pruferPeel T (n - 2)).2.count k + 1 := by
  haveI : NeZero n := ⟨by omega⟩
  rw [← ofFn_pruferEncode_eq' T]
  exact GYGraphTheory.prop_3_7_1 hn T hT k
