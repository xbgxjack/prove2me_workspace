import Mathlib
import Definitions.Def_ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n) (heven : 2 ∣ n) :
    let m := n / 2
    1 ≤ m ∧ m < m+1 ∧ m+1 < m*(m+1) ∧
      (4 / n : ℚ) = 1 / m + 1 / (m+1 : ℕ) + 1 / (m*(m+1) : ℕ) := by
  obtain ⟨j, hj⟩ := heven
  have hm : n / 2 = j := by omega
  have hj2 : 2 ≤ j := by omega
  simp only [hm]
  refine ⟨by omega, by omega, by nlinarith, ?_⟩
  have hj' : (j:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hj1' : (j:ℚ) + 1 ≠ 0 := by positivity
  have hn' : (n:ℚ) = 2 * j := by rw [hj]; push_cast; ring
  rw [hn']
  push_cast
  field_simp
  ring
