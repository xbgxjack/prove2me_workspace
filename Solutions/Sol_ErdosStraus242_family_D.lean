import Mathlib
import Definitions.Def_ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n) (hmod : n % 8 = 5) :
    let u := (n+3)/4
    1 ≤ u ∧ u < n*u/2 ∧ n*u/2 < n*u ∧
      (4 / n : ℚ) = 1 / u + 1 / (n*u/2 : ℕ) + 1 / (n*u : ℕ) := by
  intro u
  have hu : u = (n + 3) / 4 := rfl
  have h1 : u * 4 = n + 3 := by omega
  have hu1 : 1 ≤ u := by omega
  obtain ⟨v, hv⟩ : ∃ v, u = 2 * v := ⟨u / 2, by omega⟩
  have h2 : n * u / 2 = n * v := by
    rw [hv, show n * (2 * v) = 2 * (n * v) by ring]
    exact Nat.mul_div_cancel_left (n * v) (by norm_num)
  rw [h2]
  have hv1 : 1 ≤ v := by omega
  refine ⟨hu1, by nlinarith, by nlinarith, ?_⟩
  have hu' : (u:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn' : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hv' : (v:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : (n:ℚ) + 3 = 4 * u := by
    have heq : (n:ℚ) + 3 = ((n + 3 : ℕ) : ℚ) := by push_cast; ring
    rw [heq, ← h1]
    push_cast
    ring
  have huv' : (u:ℚ) = 2 * v := by rw [hv]; push_cast; ring
  push_cast
  field_simp
  nlinarith [key, huv', mul_pos (show (0:ℚ) < n by positivity) (show (0:ℚ) < v by positivity)]
