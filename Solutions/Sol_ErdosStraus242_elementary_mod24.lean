import Mathlib
import Definitions.Def_ErdosStraus242

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n) (hmod : n % 24 ≠ 1) : IsErdosStraus n := by
  unfold IsErdosStraus
  by_cases h2 : n % 2 = 0
  · -- n even: 4/n = 2/m with m = n/2
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hm2 : 2 ≤ m := by omega
    refine ⟨m, m + 1, m * (m + 1), by omega, by omega, by nlinarith, ?_⟩
    have hm' : (m:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn' : (n:ℚ) = 2 * m := by rw [hm]; push_cast; ring
    rw [hn']; push_cast; field_simp; ring
  · by_cases h3 : n % 3 = 0
    · -- 3 ∣ n
      obtain ⟨j, hj⟩ : ∃ j, n = 3 * j := ⟨n / 3, by omega⟩
      have hj1 : 1 ≤ j := by omega
      refine ⟨j, 4 * j, 4 * n, by omega, by nlinarith, by nlinarith, ?_⟩
      have hj' : (j:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hn' : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hnj : (n:ℚ) = 3 * j := by rw [hj]; push_cast; ring
      push_cast; rw [hnj]; field_simp; ring
    · by_cases h32 : n % 3 = 2
      · -- n ≡ 2 mod 3
        obtain ⟨u, hu⟩ : ∃ u, n + 1 = 3 * u := ⟨(n + 1) / 3, by omega⟩
        have hu1 : 1 ≤ u := by omega
        refine ⟨u, n, n * u, hu1, by omega, by nlinarith, ?_⟩
        have hu' : (u:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hn' : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have key : (n:ℚ) + 1 = 3 * u := by
          have heq : (n:ℚ) + 1 = ((n + 1 : ℕ) : ℚ) := by push_cast; ring
          rw [heq, hu]; push_cast; ring
        push_cast; field_simp
        nlinarith [key]
      · by_cases h4 : n % 4 = 3
        · -- n ≡ 3 mod 4
          obtain ⟨u, hu⟩ : ∃ u, n + 1 = 4 * u := ⟨(n + 1) / 4, by omega⟩
          have hu1 : 1 ≤ u := by omega
          set t := n * u with ht
          have ht3 : 3 ≤ t := by
            have hge : n * 1 ≤ n * u := by gcongr
            simp only [mul_one] at hge
            omega
          refine ⟨u, t + 1, t * (t + 1), hu1, by nlinarith, by nlinarith, ?_⟩
          have hu' : (u:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have hn' : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have ht' : (t:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have key : (n:ℚ) + 1 = 4 * u := by
            have heq : (n:ℚ) + 1 = ((n + 1 : ℕ) : ℚ) := by push_cast; ring
            rw [heq, hu]; push_cast; ring
          have htn : (t:ℚ) = n * u := by rw [ht]; push_cast; ring
          push_cast; field_simp
          linear_combination (((4*(u:ℚ) - n)*(t + n*u) + (4*(u:ℚ) - n - n*u))) * htn -
            ((n:ℚ)*u*(n*u+1)) * key
        · by_cases h8 : n % 8 = 5
          · -- n ≡ 5 mod 8
            obtain ⟨u, hu⟩ : ∃ u, n + 3 = 4 * u := ⟨(n + 3) / 4, by omega⟩
            have hu1 : 1 ≤ u := by omega
            obtain ⟨v, hv⟩ : ∃ v, u = 2 * v := ⟨u / 2, by omega⟩
            have hv1 : 1 ≤ v := by omega
            refine ⟨u, n * v, n * u, hu1, by nlinarith, by nlinarith, ?_⟩
            have hu' : (u:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have hn' : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have hv' : (v:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have key : (n:ℚ) + 3 = 4 * u := by
              have heq : (n:ℚ) + 3 = ((n + 3 : ℕ) : ℚ) := by push_cast; ring
              rw [heq, hu]; push_cast; ring
            have huv' : (u:ℚ) = 2 * v := by rw [hv]; push_cast; ring
            push_cast; field_simp
            nlinarith [key, huv', mul_pos (show (0:ℚ) < n by positivity) (show (0:ℚ) < v by positivity)]
          · exfalso; omega
