import Mathlib
import Definitions.Def_ErdosStraus242
import Theorems.Thm_ErdosStraus242_elementary_mod24
import Theorems.Thm_ErdosStraus242_scaling

open ErdosStraus242

theorem solution :
    (∀ n : ℕ, 2 < n → IsErdosStraus n) ↔
    (∀ p : ℕ, Nat.Prime p → p % 24 = 1 → IsErdosStraus p) := by
  constructor
  · intro h p hp hmod
    have hp2 := hp.two_le
    exact h p (by omega)
  · intro h n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases hmod : n % 24 = 1
      · by_cases hprime : Nat.Prime n
        · exact h n hprime hmod
        · obtain ⟨q, hq_prime, q_dvd⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
          obtain ⟨m, hm⟩ := q_dvd
          have hq2 : 2 ≤ q := hq_prime.two_le
          have hm_pos : 0 < m := by
            rcases Nat.eq_zero_or_pos m with h0 | h0
            · rw [h0, mul_zero] at hm; omega
            · exact h0
          have hm_ne1 : m ≠ 1 := by
            intro h1
            rw [h1, mul_one] at hm
            exact hprime (hm ▸ hq_prime)
          have hm2 : 2 ≤ m := by omega
          have hqlt : q < n := by
            rw [hm]
            nlinarith
          have hq_gt2 : 2 < q := by
            rcases (show q = 2 ∨ 2 < q by omega) with h2 | h2
            · exfalso
              rw [h2] at hm
              omega
            · exact h2
          have hqIH := ih q hqlt hq_gt2
          rw [hm, mul_comm]
          exact scaling q m hqIH hm_pos
      · exact elementary_mod24 n hn hmod
