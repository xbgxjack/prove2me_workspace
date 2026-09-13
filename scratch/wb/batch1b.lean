import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

/- base_31532 : a+b+c = -6 ⊢ a²b²+b²c²+c²a²+12abc+48 ≥ 0.
   Eliminate c and work with a degree-4 polynomial in two variables, whose only
   zero is a = b = -2. -/
theorem s31532 (a b c : ℝ) (h : a + b + c = -6) :
    a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 12 * a * b * c + 48 ≥ 0 := by
  have hc : c = -6 - a - b := by linarith
  subst hc
  nlinarith [sq_nonneg (a + 2), sq_nonneg (b + 2), sq_nonneg (a - b),
    sq_nonneg ((a + 2) * (b + 2)), sq_nonneg (a + b + 4),
    sq_nonneg (a*b + 2*a + 2*b), sq_nonneg (a*b - 4),
    sq_nonneg ((a + 2) * (a + b + 4)), sq_nonneg ((b + 2) * (a + b + 4)),
    sq_nonneg (a^2 + a*b + b^2 - 12)]

/- base_11560 : a+b+c = 0 ⊢ a²b²+a²c²+b²c²+3 ≥ 6abc.
   With c = -a-b the claim is (a²+ab+b²)² + 6ab(a+b) + 3 ≥ 0, tight at
   (-1,-1), (-1,2) and (2,-1) — all of which satisfy a²+ab+b² = 3. -/
theorem s11560 (a b c : ℝ) (habc : a + b + c = 0) :
    a^2 * b^2 + a^2 * c^2 + b^2 * c^2 + 3 ≥ 6 * a * b * c := by
  have hc : c = -a - b := by linarith
  subst hc
  nlinarith [sq_nonneg (a^2 + a*b + b^2 - 3), sq_nonneg (a - b), sq_nonneg (a + b),
    sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (a + b + 2),
    sq_nonneg ((a + 1) * (b + 1)), sq_nonneg (a*b + a + b - 1),
    sq_nonneg ((a - b) * (a + b + 2)), sq_nonneg (a*b - a - b - 2)]
