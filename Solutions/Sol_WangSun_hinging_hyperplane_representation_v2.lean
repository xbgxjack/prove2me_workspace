import Definitions.Def_CPWL
import Theorems.Thm_WangSun_Main_shared

open Finset

theorem solution {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : CPWL f) : IsHH f :=
  WangSun.Main_shared hf
