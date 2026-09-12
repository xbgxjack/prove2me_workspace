import Mathlib

namespace Katona

/-- **Katona's union theorem** (even case). A family of subsets of an `n`-element set
whose pairwise unions all have size at most `2d` has size at most the Hamming ball of
radius `d`, i.e. `∑_{i=0}^{d} C(n,i)`. -/
theorem katona_union {n d : ℕ} (hd : 2 * d < n) (F : Finset (Finset (Fin n)))
    (hF : ∀ A ∈ F, ∀ B ∈ F, (A ∪ B).card ≤ 2 * d) :
    F.card ≤ ∑ i ∈ Finset.range (d + 1), n.choose i := by sorry

end Katona
