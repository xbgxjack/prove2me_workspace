import Mathlib

/-- The graph search framework of Bertsekas, "Dynamic Programming and Optimal
Control", Vol. I, 3rd ed., Section 6.4.1 (discrete deterministic problems):
a finite directed graph with arc set `arcs`, a set `dest` of destination
nodes, and a cost `cost i` for terminating at each destination node `i`. -/
structure BertsekasGraphSearch (V : Type) [Fintype V] [DecidableEq V] where
  arcs : Finset (V × V)
  dest : Finset V
  cost : V → ℝ

open Classical in
/-- The set `N(i)` of downstream neighbors of a node `i`:
`N(i) = {j | (i, j) is an arc}`. -/
noncomputable def BertsekasNbrs {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasGraphSearch V) (i : V) : Finset V :=
  (G.arcs.filter fun a => a.1 = i).image Prod.snd

/-- A base heuristic `H` in the sense of Section 6.4.1: a path construction
algorithm which, from every non-destination node `i`, produces a path in the
graph starting at `i` and ending at a destination node.  By convention, from a
destination node it produces the degenerate path `[i]`. -/
structure BertsekasBaseHeuristic {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasGraphSearch V) where
  path : V → List V
  hstart : ∀ i, (path i).head? = some i
  hchain : ∀ i, i ∉ G.dest → List.IsChain (fun a b => (a, b) ∈ G.arcs) (path i)
  hend : ∀ i, ∃ d ∈ G.dest, (path i).getLast? = some d
  hdest : ∀ i ∈ G.dest, path i = [i]

/-- The projection `p(i)` of a node `i` under a base heuristic: the destination
node at which the heuristic's path from `i` ends. -/
def BertsekasProjection {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasGraphSearch V) (H : BertsekasBaseHeuristic G) (i : V) : V :=
  ((H.path i).getLast?).getD i

/-- The cost `H(i) = g(p(i))` associated with a node `i` by a base heuristic:
the cost of the destination (projection) reached by the heuristic's path from
`i`.  For a destination node, `H(i) = g(i)`. -/
def BertsekasHeurCost {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasGraphSearch V) (H : BertsekasBaseHeuristic G) (i : V) : ℝ :=
  G.cost (BertsekasProjection G H i)

/-- Definition 6.4.1 of Bertsekas, Vol. I, 3rd ed.: a base heuristic `H` is
sequentially consistent if whenever it generates the path `(i, i₁, …, i_m, ī)`
starting from `i`, it generates the path `(i₁, …, i_m, ī)` starting from `i₁`.
Equivalently, all nodes of a generated path have the same projection. -/
def BertsekasSeqConsistent {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasGraphSearch V) (H : BertsekasBaseHeuristic G) : Prop :=
  ∀ i ∉ G.dest, ∀ (j : V) (l : List V),
    H.path i = i :: j :: l → H.path j = j :: l

/-- Definition 6.4.2 of Bertsekas, Vol. I, 3rd ed.: a base heuristic `H` is
sequentially improving if for every non-destination node `i`,
`H(i) ≥ min_{j ∈ N(i)} H(j)`. -/
def BertsekasSeqImproving {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasGraphSearch V) (H : BertsekasBaseHeuristic G) : Prop :=
  ∀ i ∉ G.dest, ∀ hne : (BertsekasNbrs G i).Nonempty,
    (BertsekasNbrs G i).inf' hne (BertsekasHeurCost G H) ≤
      BertsekasHeurCost G H i

/-- A (complete, finite) run of the rollout algorithm `RH` of Section 6.4.1:
a nonempty node sequence in which every node but the last is a
non-destination node, each node is followed by a neighbor of minimal heuristic
cost `H` (Eq. (6.33)), and the last node is a destination. -/
def BertsekasIsRolloutRun {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasGraphSearch V) (H : BertsekasBaseHeuristic G)
    (l : List V) : Prop :=
  l ≠ [] ∧
  List.IsChain (fun a b => b ∈ BertsekasNbrs G a ∧
    ∀ j ∈ BertsekasNbrs G a,
      BertsekasHeurCost G H b ≤ BertsekasHeurCost G H j) l ∧
  (∀ v ∈ l.dropLast, v ∉ G.dest) ∧
  (∃ d ∈ G.dest, l.getLast? = some d)

open Classical in
/-- The quantity `δ_i = min_{j ∈ N(i)} H(j) - H(i)` of Prop. 6.4.3 of
Bertsekas, Vol. I, 3rd ed. (junk value `0` when `i` has no neighbors). -/
noncomputable def BertsekasRolloutDelta {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasGraphSearch V) (H : BertsekasBaseHeuristic G) (i : V) : ℝ :=
  if hne : (BertsekasNbrs G i).Nonempty then
    (BertsekasNbrs G i).inf' hne (BertsekasHeurCost G H) -
      BertsekasHeurCost G H i
  else 0
