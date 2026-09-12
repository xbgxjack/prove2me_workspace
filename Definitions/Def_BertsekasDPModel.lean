import Mathlib

/-- The basic finite-horizon stochastic optimal control model of Bertsekas,
"Dynamic Programming and Optimal Control", Vol. I, 3rd ed., Section 1.2,
with finite disturbance space and finite control-constraint sets.
`f` is the system equation, `g` the stage cost, `gN` the terminal cost,
`U k x` the control constraint set at stage `k` and state `x`, and
`p k x u w` the probability that the stage-`k` disturbance equals `w`
given state `x` and control `u` (a probability distribution for every
admissible control `u ∈ U k x`). -/
structure BertsekasDPModel (S C W : Type) [Fintype W] where
  N : ℕ
  f : ℕ → S → C → W → S
  g : ℕ → S → C → W → ℝ
  gN : S → ℝ
  U : ℕ → S → Finset C
  hU : ∀ k x, (U k x).Nonempty
  p : ℕ → S → C → W → ℝ
  hp_nonneg : ∀ k x, ∀ u ∈ U k x, ∀ w, 0 ≤ p k x u w
  hp_sum : ∀ k x, ∀ u ∈ U k x, ∑ w, p k x u w = 1

/-- Expected cost-to-go of a policy `π` in the basic problem, by backward
recursion on the number `m` of remaining stages: `BertsekasDPPolicyCost M π m x`
is the expected cost of the last `m` stages when the state at stage `M.N - m`
is `x` and controls are chosen by `π`.  The total expected cost of `π` from
initial state `x₀` is `BertsekasDPPolicyCost M π M.N x₀`. -/
def BertsekasDPPolicyCost {S C W : Type} [Fintype W] (M : BertsekasDPModel S C W)
    (π : ℕ → S → C) : ℕ → S → ℝ
  | 0, x => M.gN x
  | m + 1, x =>
      let k := M.N - (m + 1)
      let u := π k x
      ∑ w, M.p k x u w * (M.g k x u w + BertsekasDPPolicyCost M π m (M.f k x u w))

/-- The dynamic programming (value iteration) algorithm of Prop. 1.3.1:
`BertsekasDPValue M m x` is `J_{N-m}(x)`, computed backward from the terminal
condition `J_N = g_N` by minimizing the expected current stage cost plus
cost-to-go over the finite control constraint set. -/
noncomputable def BertsekasDPValue {S C W : Type} [Fintype W]
    (M : BertsekasDPModel S C W) : ℕ → S → ℝ
  | 0, x => M.gN x
  | m + 1, x =>
      let k := M.N - (m + 1)
      (M.U k x).inf' (M.hU k x) fun u =>
        ∑ w, M.p k x u w * (M.g k x u w + BertsekasDPValue M m (M.f k x u w))
