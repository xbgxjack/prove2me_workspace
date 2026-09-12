import Mathlib

open Finset

namespace Erdos287

/-- A block of consecutive integers none of whose members is divisible by `2 ^ (c+1)` has
length at most `2 ^ (c+1) - 1`. -/
theorem block_two_adic_length (c m t : ℕ) (hm : 0 < m)
    (h : ∀ j, j < t → padicValNat 2 (m + j) ≤ c) :
    t ≤ 2 ^ (c + 1) - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push_neg at hcon
  have hqpos : 0 < 2 ^ (c + 1) := pow_pos (by norm_num) _
  have hlt : m % 2 ^ (c + 1) < 2 ^ (c + 1) := Nat.mod_lt _ hqpos
  have hmr : m = 2 ^ (c + 1) * (m / 2 ^ (c + 1)) + m % 2 ^ (c + 1) :=
    (Nat.div_add_mod m (2 ^ (c + 1))).symm
  set j := (2 ^ (c + 1) - m % 2 ^ (c + 1)) % 2 ^ (c + 1) with hj
  have hjq : j < 2 ^ (c + 1) := Nat.mod_lt _ hqpos
  have hjt : j < t := by omega
  have hdvd : 2 ^ (c + 1) ∣ (m + j) := by
    rcases Nat.eq_zero_or_pos (m % 2 ^ (c + 1)) with h0 | h0
    · refine ⟨m / 2 ^ (c + 1), ?_⟩
      have hj0 : j = 0 := by rw [hj, h0, Nat.sub_zero, Nat.mod_self]
      omega
    · have hjeq : j = 2 ^ (c + 1) - m % 2 ^ (c + 1) := by
        rw [hj]; exact Nat.mod_eq_of_lt (by omega)
      refine ⟨m / 2 ^ (c + 1) + 1, ?_⟩
      rw [Nat.mul_add, Nat.mul_one, hjeq]
      omega
  have h1 : c + 1 ≤ padicValNat 2 (m + j) := (padicValNat_dvd_iff_le (by omega)).mp hdvd
  have h2 := h j hjt
  omega

end Erdos287
