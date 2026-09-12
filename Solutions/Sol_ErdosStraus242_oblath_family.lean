import Mathlib
import Definitions.Def_ErdosStraus242
import Theorems.Thm_ErdosStraus242_even_family

open ErdosStraus242

theorem solution (n q : ℕ) (hn : 2 < n)
    (hq : Nat.Prime q) (hdiv : q ∣ n+1) (hmod : q % 4 = 3) :
    IsErdosStraus n := by
  by_cases heven : 2 ∣ n
  · have h := even_family n hn heven
    exact ⟨n / 2, n / 2 + 1, n / 2 * (n / 2 + 1), h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  · obtain ⟨k, hk⟩ := hdiv
    have hqodd : q % 2 = 1 := by omega
    have hkeven : k % 2 = 0 := by
      have h1 : (q * k) % 2 = (q % 2) * (k % 2) % 2 := Nat.mul_mod q k 2
      rw [hqodd] at h1
      omega
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, mul_zero] at hk; omega
      · exact h0
    have hk2 : 2 ≤ k := by omega
    have hqpos : 0 < q := hq.pos
    set d := (q + 1) / 4 with hd
    have hd4 : d * 4 = q + 1 := by omega
    have hdpos : 0 < d := by omega
    refine ⟨k * d, d * n, k * d * n, ?_, ?_, ?_, ?_⟩
    · exact Nat.mul_pos hkpos hdpos
    · have hq3 : q ≥ 3 := by omega
      have hkn : k < n := by nlinarith [hk, hq3, hk2]
      nlinarith [hkn, hdpos]
    · have hdn : 0 < d * n := Nat.mul_pos hdpos (by omega)
      have := Nat.mul_le_mul_right (d * n) hk2
      nlinarith [this, hdn]
    · have hd' : (d:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hn' : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hk' : (k:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h1 : (d:ℚ) * 4 = q + 1 := by exact_mod_cast hd4
      have h2 : (n:ℚ) + 1 = q * k := by exact_mod_cast hk
      have key : (n:ℚ) + 1 + k = 4 * k * d := by nlinarith [h1, h2]
      push_cast
      field_simp
      nlinarith [key]
