import Mathlib

/-!
Definitions for the GYGraphTheory mission proposal (Cayley's Tree Formula).
Source: J.L. Gross and J. Yellen, *Graph Theory and Its Applications*, 3rd ed.,
CRC Press, 2018, Section 3.7 "Counting Labeled Trees: Prüfer Encoding", pp. 157-162.
-/

noncomputable section
open Classical

namespace GYGraphTheory

variable {n : ℕ} [NeZero n]

/-- The neighbors of `v` lying in the active vertex set `S` (Gross–Yellen, p. 157: the
neighbor set used when peeling leaves during Prüfer encoding). -/
def activeNeighbors (T : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : Finset (Fin n) :=
  S.filter (fun w => T.Adj v w)

/-- `v` is a leaf of `T` relative to the active set `S`: an element of `S` with exactly one
neighbor still in `S`. -/
def IsActiveLeaf (T : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : Prop :=
  v ∈ S ∧ (activeNeighbors T S v).card = 1

/-- The smallest-labeled active leaf of `T` in `S` (Algorithm 3.7.1, p. 157: "Let `v` be the
1-valent vertex with the smallest label"). Junk-valued (`0`) when `S` has no active leaf,
i.e. outside the intended range `2 ≤ S.card`. -/
def leastActiveLeaf (T : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Fin n :=
  (S.filter (IsActiveLeaf T S)).min.getD 0

/-- The unique neighbor, inside `S`, of the smallest-labeled active leaf of `T` in `S`
(Algorithm 3.7.1, p. 157: "Let `s_i` be the label of the neighbor of `v`"). Junk-valued when
that leaf has no such neighbor. -/
def leastActiveLeafNeighbor (T : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Fin n :=
  (activeNeighbors T S (leastActiveLeaf T S)).min.getD 0

/-- One step of Prüfer encoding: peel the smallest-labeled active leaf out of `S`, recording
its neighbor. Iterating this `n - 2` times from `S = Finset.univ` produces the Prüfer
sequence (Algorithm 3.7.1, p. 157). -/
def pruferPeel (T : SimpleGraph (Fin n)) : ℕ → Finset (Fin n) × List (Fin n)
  | 0 => (Finset.univ, [])
  | k + 1 =>
      let (S, acc) := pruferPeel T k
      (S.erase (leastActiveLeaf T S), acc ++ [leastActiveLeafNeighbor T S])

/-- The Prüfer encoding of a labeled tree `T` on `Fin n` (Algorithm 3.7.1, p. 157): the
length-`(n - 2)` sequence of neighbor-labels recorded while repeatedly peeling off the
smallest-labeled leaf. -/
def pruferEncode (T : SimpleGraph (Fin n)) (i : Fin (n - 2)) : Fin n :=
  (pruferPeel T (i.1 + 1)).2.getD i.1 0

/-- Prüfer decoding (Algorithm 3.7.3, p. 159), recursing on the remaining sequence `P` while
tracking the shrinking active label-set `L`. Builds the tree by adding, at each step, an edge
from the smallest label in `L` absent from `P` to the head of `P`; the base case (`P = []`,
so `L` has the two labels left over) is the single edge joining them. Junk-valued (no edge)
wherever `L` does not have the expected size, i.e. outside the intended recursive shape. -/
def pruferDecodeAux : List (Fin n) → Finset (Fin n) → SimpleGraph (Fin n)
  | [], L =>
      let a := L.min.getD 0
      let b := (L.erase a).min.getD 0
      SimpleGraph.fromEdgeSet {s(a, b)}
  | p :: ps, L =>
      let k := (L \ (p :: ps).toFinset).min.getD 0
      pruferDecodeAux ps (L.erase k) ⊔ SimpleGraph.fromEdgeSet {s(k, p)}

/-- The Prüfer decoding of a sequence into a labeled tree on `Fin n` (Algorithm 3.7.3, p. 159). -/
def pruferDecode (s : Fin (n - 2) → Fin n) : SimpleGraph (Fin n) :=
  pruferDecodeAux (List.ofFn s) Finset.univ

end GYGraphTheory
