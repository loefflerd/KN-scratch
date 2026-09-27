import Mathlib
import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane in
theorem ModularCurve.exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq (N d : ℕ)
    [NeZero N] [NeZero d] (hd : d ∣ N) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
      ModularCurve.coeffEmb ℂ (ModularCurve.qExpand ℚ d ModularCurve.jq) *
          ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by sorry
