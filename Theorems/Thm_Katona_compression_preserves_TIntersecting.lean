import Mathlib
import Definitions.Def_Katona

open Finset UV
open scoped FinsetFamily

namespace Katona

theorem compression_preserves_TIntersecting {n : ℕ} (z i : Fin n) (hzi : z ≠ i) (t : ℕ)
    {𝒜 : Finset (Finset (Fin n))} (h𝒜 : TIntersecting t 𝒜) :
    TIntersecting t (𝓒 ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) 𝒜) := by sorry

end Katona
