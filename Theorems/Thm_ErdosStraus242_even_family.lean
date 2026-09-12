import Definitions.Def_ErdosStraus242

namespace ErdosStraus242

theorem even_family (n : ℕ) (hn : 2 < n) (heven : 2 ∣ n) :
    let m := n / 2
    1 ≤ m ∧ m < m+1 ∧ m+1 < m*(m+1) ∧
      (4 / n : ℚ) = 1 / m + 1 / (m+1 : ℕ) + 1 / (m*(m+1) : ℕ) := by
  sorry

end ErdosStraus242
