import Mathlib
open Finset

private lemma geom (m a : ℕ) :
    m * (∑ i ∈ Finset.range (a + 1), (m + 1) ^ i) + 1 = (m + 1) ^ (a + 1) := by
  induction a with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, add_assoc, add_comm (m * (m + 1) ^ (k + 1)) 1,
        ← add_assoc, ih]
      ring

private lemma sigma_pow_lt (p a : ℕ) (hp : p.Prime) :
    (p - 1) * ArithmeticFunction.sigma 1 (p ^ a) < p * p ^ a := by
  have hp2 : 2 ≤ p := hp.two_le
  have hsig : ArithmeticFunction.sigma 1 (p ^ a) = ∑ i ∈ Finset.range (a + 1), p ^ i := by
    rw [ArithmeticFunction.sigma_apply, Nat.sum_divisors_prime_pow hp]
    simp
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have hg := geom m a
  rw [hsig]
  simp only [Nat.add_sub_cancel]
  have : (m + 1) * (m + 1) ^ a = (m + 1) ^ (a + 1) := by ring
  rw [this, ← hg]
  omega

theorem solution (n : Nat) (hn : 1 < n) :
    (∏ q ∈ n.primeFactors, (q - 1)) * ArithmeticFunction.sigma 1 n <
      (∏ q ∈ n.primeFactors, q) * n := by
  have hn0 : n ≠ 0 := by omega
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
  -- σ is multiplicative
  have hsig : ArithmeticFunction.sigma 1 n
      = ∏ p ∈ n.primeFactors, ArithmeticFunction.sigma 1 (p ^ n.factorization p) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn0]
    rfl
  have hself : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
    rfl
  have hlt : ∀ p ∈ n.primeFactors,
      (p - 1) * ArithmeticFunction.sigma 1 (p ^ n.factorization p)
        < p * p ^ n.factorization p :=
    fun p hp => sigma_pow_lt p _ (Nat.prime_of_mem_primeFactors hp)
  have hpos : ∀ p ∈ n.primeFactors,
      0 < (p - 1) * ArithmeticFunction.sigma 1 (p ^ n.factorization p) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h1 : 0 < p - 1 := by have := hpp.two_le; omega
    have hpz : p ^ n.factorization p ≠ 0 := pow_ne_zero _ hpp.ne_zero
    have h2 : 0 < ArithmeticFunction.sigma 1 (p ^ n.factorization p) :=
      Nat.pos_of_ne_zero fun h => hpz (ArithmeticFunction.sigma_eq_zero.mp h)
    exact Nat.mul_pos h1 h2
  have hprod := Finset.prod_lt_prod_of_nonempty (s := n.primeFactors)
    (f := fun p => (p - 1) * ArithmeticFunction.sigma 1 (p ^ n.factorization p))
    (g := fun p => p * p ^ n.factorization p) hpos hlt hne
  calc (∏ q ∈ n.primeFactors, (q - 1)) * ArithmeticFunction.sigma 1 n
      = ∏ p ∈ n.primeFactors, ((p - 1) * ArithmeticFunction.sigma 1 (p ^ n.factorization p)) := by
        rw [hsig, ← Finset.prod_mul_distrib]
    _ < ∏ p ∈ n.primeFactors, (p * p ^ n.factorization p) := hprod
    _ = (∏ q ∈ n.primeFactors, q) * n := by
        rw [Finset.prod_mul_distrib, ← hself]
