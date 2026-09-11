import Mathlib
import Definitions.Def_ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n) (hmod : n % 4 = 3) :
    let u := (n+1)/4
    let t := n*u
    1 ≤ u ∧ u < t+1 ∧ t+1 < t*(t+1) ∧
      (4 / n : ℚ) = 1 / u + 1 / (t+1 : ℕ) + 1 / (t*(t+1) : ℕ) := by
  have h1 : (n+1)/4 * 4 = n + 1 := by omega
  set u := (n+1)/4 with hu
  set t := n * u with ht
  have hu1 : 1 ≤ u := by omega
  have ht3 : 3 ≤ t := by
    have hge : n * 1 ≤ n * u := by gcongr
    simp only [mul_one] at hge
    omega
  refine ⟨hu1, by nlinarith, by nlinarith, ?_⟩
  have hu' : (u:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn' : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ht' : (t:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : (n:ℚ) + 1 = 4 * u := by
    have heq : (n:ℚ) + 1 = ((n+1 : ℕ) : ℚ) := by push_cast; ring
    rw [heq, ← h1]
    push_cast
    ring
  have htn : (t:ℚ) = n * u := by rw [ht]; push_cast; ring
  push_cast
  field_simp
  nlinarith [key, htn, mul_pos (show (0:ℚ) < n by positivity) (show (0:ℚ) < u by positivity)]
