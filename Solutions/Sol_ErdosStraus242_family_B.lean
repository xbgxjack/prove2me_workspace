import Mathlib
import Definitions.Def_ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n) (hmod : n % 3 = 2) :
    let u := (n+1)/3
    1 ≤ u ∧ u < n ∧ n < n*u ∧
      (4 / n : ℚ) = 1 / u + 1 / n + 1 / (n*u : ℕ) := by
  have h1 : (n+1)/3 * 3 = n + 1 := by omega
  set u := (n+1)/3 with hu
  have hn3 : n = 3 * u - 1 := by omega
  have hu1 : 1 ≤ u := by omega
  refine ⟨hu1, by omega, by nlinarith, ?_⟩
  have hu' : (u:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn' : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : (n:ℚ) + 1 = 3 * u := by
    have : (n:ℚ) + 1 = ((n+1 : ℕ) : ℚ) := by push_cast; ring
    rw [this, ← h1]
    push_cast
    ring
  push_cast
  field_simp
  nlinarith [key]
