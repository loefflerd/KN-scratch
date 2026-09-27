import Mathlib
import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_ModularCurve_LaurentCoeff
import Definitions.FLT.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m)
    (X : LaurentSeries ℂ)
    (hX : X ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) (M : ℕ)
    (h₁ : IsIntegral (Algebra.adjoin ℂ ({ModularCurve.coeffEmb ℂ ModularCurve.jq} : Set (LaurentSeries ℂ)))
      (X ^ 6 * ModularCurve.coeffEmb ℂ ModularCurve.jq ^ (4 * m) *
        (ModularCurve.coeffEmb ℂ ModularCurve.jq - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * m)))
    (h₂ : IsIntegral (Algebra.adjoin ℂ ({(ModularCurve.coeffEmb ℂ ModularCurve.jq)⁻¹} : Set (LaurentSeries ℂ)))
      (X ^ (2 * M) * ModularCurve.coeffEmb ℂ ModularCurve.jq ^ (m * M + 1) *
        (ModularCurve.coeffEmb ℂ ModularCurve.jq - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (m * M))) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ)),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 f) =
        X * ModularCurve.thetaL ℂ (ModularCurve.coeffEmb ℂ ModularCurve.jq) ^ m := by sorry
