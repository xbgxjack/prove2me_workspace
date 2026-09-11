import Mathlib
import Definitions.Def_ErdosStraus242
import Theorems.Thm_ErdosStraus242_elementary_mod24

set_option maxHeartbeats 1000000

open ErdosStraus242

private theorem key_construction (n a c d b : ℕ) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (hb : 0 < b) (hcong : c * n + a + b = 4 * a * b * c * d)
    (hxy : a * b * d < a * c * d * n) (hyz : a * c * d * n < b * c * d * n) :
    IsErdosStraus n := by
  refine ⟨a * b * d, a * c * d * n, b * c * d * n, ?_, hxy, hyz, ?_⟩
  · exact Nat.mul_pos (Nat.mul_pos ha hb) hd
  · have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exfalso; rw [h0, mul_zero] at hxy; omega
      · exact h0
    have ha' : (a:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hb' : (b:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hc' : (c:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hd' : (d:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn' : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have key : (c:ℚ) * n + a + b = 4 * a * b * c * d := by exact_mod_cast hcong
    push_cast
    field_simp
    nlinarith [key]

theorem solution (p : ℕ) (hp : Nat.Prime p) (hp2 : 2 < p)
    (hres : p % 840 ∉ ({1, 121, 169, 289, 361, 529} : Finset ℕ)) :
    IsErdosStraus p := by
  by_cases h24 : p % 24 = 1
  · -- p is coprime to 5 and 7 here, since p prime, p ≠ 5, p ≠ 7 (as 5 % 24 ≠ 1, 7 % 24 ≠ 1)
    have hp5 : p % 5 ≠ 0 := by
      intro h
      have h5dvd : (5:ℕ) ∣ p := Nat.dvd_of_mod_eq_zero h
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h5dvd
      omega
    have hp7 : p % 7 ≠ 0 := by
      intro h
      have h7dvd : (7:ℕ) ∣ p := Nat.dvd_of_mod_eq_zero h
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h7dvd
      omega
    by_cases h7a : p % 7 = 3
    · obtain ⟨b, hb⟩ : ∃ b, 2 * p + 1 = 7 * b := ⟨(2 * p + 1) / 7, by omega⟩
      have hab : 1 < b := by omega
      have hbc : b < 2 * p := by omega
      exact key_construction p 1 2 1 b (by norm_num) (by norm_num) (by norm_num) (by omega)
        (by ring_nf; omega) (by nlinarith) (by nlinarith)
    · by_cases h7b : p % 7 = 6
      · obtain ⟨b, hb⟩ : ∃ b, p + 1 = 7 * b := ⟨(p + 1) / 7, by omega⟩
        have hab : 1 < b := by omega
        have hbc : b < p := by omega
        exact key_construction p 1 1 2 b (by norm_num) (by norm_num) (by norm_num) (by omega)
          (by ring_nf; omega) (by nlinarith) (by nlinarith)
      · by_cases h7c : p % 7 = 5
        · obtain ⟨b, hb⟩ : ∃ b, p + 2 = 7 * b := ⟨(p + 2) / 7, by omega⟩
          have hab : 2 < b := by omega
          have hbc : b < p := by omega
          exact key_construction p 2 1 1 b (by norm_num) (by norm_num) (by norm_num) (by omega)
            (by ring_nf; omega) (by nlinarith) (by nlinarith)
        · -- p % 7 ∈ {1, 2, 4}
          by_cases h5a : p % 5 = 3
          · obtain ⟨b, hb⟩ : ∃ b, p + 2 = 15 * b := ⟨(p + 2) / 15, by omega⟩
            have hab : 2 < b := by omega
            have hbc : b < p := by omega
            exact key_construction p 2 1 2 b (by norm_num) (by norm_num) (by norm_num) (by omega)
              (by ring_nf; omega) (by nlinarith) (by nlinarith)
          · by_cases h5b : p % 5 = 2
            · obtain ⟨b, hb⟩ : ∃ b, 2 * p + 1 = 15 * b := ⟨(2 * p + 1) / 15, by omega⟩
              have hab : 1 < b := by omega
              have hbc : b < 2 * p := by omega
              exact key_construction p 1 2 2 b (by norm_num) (by norm_num) (by norm_num) (by omega)
                (by ring_nf; omega) (by nlinarith) (by nlinarith)
            · -- p % 5 ∈ {1, 4}, p % 7 ∈ {1, 2, 4}, p % 24 = 1: exactly the six hard squares mod 840
              exfalso
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hres
              obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hres
              have h7 : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 := by omega
              have h5 : p % 5 = 1 ∨ p % 5 = 4 := by omega
              have hr24 : (p % 840) % 24 = p % 24 := Nat.mod_mod_of_dvd p (by norm_num)
              have hr5 : (p % 840) % 5 = p % 5 := Nat.mod_mod_of_dvd p (by norm_num)
              have hr7 : (p % 840) % 7 = p % 7 := Nat.mod_mod_of_dvd p (by norm_num)
              have hrlt : p % 840 < 840 := Nat.mod_lt _ (by norm_num)
              rcases h7 with h7 | h7 | h7 <;> rcases h5 with h5 | h5 <;>
                rw [h24] at hr24 <;> rw [h7] at hr7 <;> rw [h5] at hr5 <;> omega
  · exact elementary_mod24 p hp2 h24
