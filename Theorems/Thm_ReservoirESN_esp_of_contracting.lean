import Mathlib
import Definitions.Def_ReservoirESN

namespace ReservoirESN

theorem esp_of_contracting {E S : Type*} [NormedAddCommGroup E] [NormedAddCommGroup S]
    [CompleteSpace S] (F : S → E → S) (L M r : ℝ)
    (hF : IsContracting F L M r) (z : ℕ → E) (hz : UnifBdd M z) :
    ∃! x : ℕ → S, UnifBdd L x ∧ IsSolution F z x := by sorry

end ReservoirESN
