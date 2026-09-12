import Mathlib
import Definitions.Def_ErdosStraus242

theorem solution (n x y z k : ℕ) (hk : 0 < k)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (h : (4 / n : ℚ) = 1 / x + 1 / y + 1 / z) :
    1 ≤ k*x ∧ k*x < k*y ∧ k*y < k*z ∧
      (4 / (k*n) : ℚ) = 1 / (k*x) + 1 / (k*y) + 1 / (k*z) := by
  refine ⟨Nat.mul_pos hk (by omega), mul_lt_mul_of_pos_left hxy hk,
    mul_lt_mul_of_pos_left hyz hk, ?_⟩
  have hk' : (k:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  push_cast
  rw [mul_comm (k:ℚ) n, div_mul_eq_div_div, h]
  field_simp
