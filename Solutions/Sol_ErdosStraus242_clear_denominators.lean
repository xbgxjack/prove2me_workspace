import Mathlib
import Definitions.Def_ErdosStraus242

theorem solution (n x y z : ℕ)
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ((4 / n : ℚ) = 1 / x + 1 / y + 1 / z) ↔
    (4 * (x : ℤ) * y * z = (n : ℤ) * (y * z + x * z + x * y)) := by
  have hn' : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hx' : (x:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  rw [show (4 * (x : ℤ) * y * z = (n : ℤ) * (y * z + x * z + x * y)) ↔
        ((4 * (x : ℤ) * y * z : ℚ) = ((n : ℤ) * (y * z + x * z + x * y) : ℚ)) from
      ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩]
  push_cast
  rw [div_add_div _ _ hx' hy', div_add_div _ _ (mul_ne_zero hx' hy') hz',
    div_eq_div_iff hn' (mul_ne_zero (mul_ne_zero hx' hy') hz')]
  constructor <;> intro h <;> linear_combination h
