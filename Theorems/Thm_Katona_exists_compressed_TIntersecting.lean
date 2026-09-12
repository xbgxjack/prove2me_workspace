import Mathlib
import Definitions.Def_TIntersecting

open Finset UV
open scoped FinsetFamily

namespace Katona

theorem exists_compressed_TIntersecting {n : ℕ} (t : ℕ) (z : Fin n) (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : TIntersecting t 𝒜) :
    ∃ ℬ : Finset (Finset (Fin n)), 𝒜.card = ℬ.card ∧ TIntersecting t ℬ ∧
      ∀ i : Fin n, (z : ℕ) < (i : ℕ) →
        IsCompressed ({z} : Finset (Fin n)) ({i} : Finset (Fin n)) ℬ := by sorry

end Katona
