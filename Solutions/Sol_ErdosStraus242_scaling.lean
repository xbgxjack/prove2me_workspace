import Mathlib
import Definitions.Def_ErdosStraus242

open ErdosStraus242

theorem solution (n k : ℕ) (h : IsErdosStraus n) (hk : 0 < k) : IsErdosStraus (k*n) := by
  obtain ⟨x, y, z, hx, hxy, hyz, heq⟩ := h
  refine ⟨k*x, k*y, k*z, Nat.mul_pos hk (by omega), mul_lt_mul_of_pos_left hxy hk,
    mul_lt_mul_of_pos_left hyz hk, ?_⟩
  have hk' : (k:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  push_cast
  rw [mul_comm (k:ℚ) n, div_mul_eq_div_div, heq]
  field_simp
