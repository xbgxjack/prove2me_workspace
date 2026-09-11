import Mathlib
import Definitions.Def_BertsekasDPModel

/-- Expected cost of a fixed (open-loop) control sequence in the basic problem
of Chapter 1: `BertsekasDPOpenLoopCost M useq m x` is the expected cost of the
last `m` stages starting from state `x` at stage `M.N - m`, when the control
at each stage `i` is the predetermined `useq i`, regardless of the state. -/
def BertsekasDPOpenLoopCost {S C W : Type} [Fintype W]
    (M : BertsekasDPModel S C W) (useq : ℕ → C) : ℕ → S → ℝ
  | 0, x => M.gN x
  | m + 1, x =>
      let k := M.N - (m + 1)
      let u := useq k
      ∑ w, M.p k x u w *
        (M.g k x u w + BertsekasDPOpenLoopCost M useq m (M.f k x u w))
