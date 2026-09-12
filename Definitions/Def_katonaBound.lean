import Mathlib

namespace Katona

/-- The extremal bound in Katona's intersection theorem: the size of a Hamming ball
of the appropriate radius, i.e. the sum of the upper `Finset.Icc ((n + t) / 2) n`
range of binomial coefficients `n.choose i`. -/
noncomputable def katonaBound (n t : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc ((n + t) / 2) n, n.choose i

end Katona
