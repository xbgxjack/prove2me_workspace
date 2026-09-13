import Mathlib
open Real Nat

set_option maxHeartbeats 1000000

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) :
    a ^ 12 + b ^ 12 + c ^ 12 + 8 * (a * b + b * c + c * a) ≥ 27 := by
  have key : ∀ t : ℝ, 0 ≤ t → 0 ≤ t^12 - 4*t^2 - 4*t + 7 := by
    intro t ht
    have e : t^12 - 4*t^2 - 4*t + 7
        = (t-1)^2 * (t^10 + 2*t^9 + 3*t^8 + 4*t^7 + 5*t^6 + 6*t^5 + 7*t^4 + 8*t^3
            + 9*t^2 + 10*t + 7) := by ring
    rw [e]
    have hpos : (0:ℝ) ≤ t^10 + 2*t^9 + 3*t^8 + 4*t^7 + 5*t^6 + 6*t^5 + 7*t^4 + 8*t^3
        + 9*t^2 + 10*t + 7 := by positivity
    exact mul_nonneg (sq_nonneg _) hpos
  have hsq : a^2 + b^2 + c^2 + 2*(a*b + b*c + c*a) = 9 := by
    linear_combination (a + b + c + 3) * hab
  linarith [key a ha.le, key b hb.le, key c hc.le, hsq, hab]
