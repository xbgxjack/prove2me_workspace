import Mathlib
import Definitions.Def_ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n) (hdiv : 3 ∣ n) :
    1 ≤ n/3 ∧ n/3 < 4*n/3 ∧ 4*n/3 < 4*n ∧
      (4 / n : ℚ) = 1 / (n/3 : ℕ) + 1 / (4*n/3 : ℕ) + 1 / (4*n : ℕ) := by
  obtain ⟨j, hj⟩ := hdiv
  have h1 : n / 3 = j := by omega
  have h2 : 4 * n / 3 = 4 * j := by omega
  have hj1 : 1 ≤ j := by omega
  rw [h1, h2]
  refine ⟨by omega, by nlinarith, by nlinarith, ?_⟩
  have hj' : (j:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn' : (n:ℚ) = 3 * j := by rw [hj]; push_cast; ring
  push_cast
  rw [hn']
  field_simp
  ring
