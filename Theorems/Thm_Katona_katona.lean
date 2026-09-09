import Mathlib
import Definitions.Def_TIntersecting
import Definitions.Def_katonaBound

open Finset UV
open scoped FinsetFamily

namespace Katona

theorem katona (n : ℕ) : ∀ t, 1 ≤ t → t ≤ n → 2 ∣ (n + t) →
    ∀ 𝒜 : Finset (Finset (Fin n)), TIntersecting t 𝒜 → 𝒜.card ≤ katonaBound n t := by sorry

end Katona
