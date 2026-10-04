import Mathlib
import Definitions.FLT.Def_ModularCurve_MazurStepThreeInputs
import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_ModularCurve_LaurentCoeff
import Definitions.FLT.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.exists_cuspForm_qExpansion_eq_coeffMap_mul_thetaL_pow_of_isIntegral (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m)
    (ι₀ : AlgebraicClosure ℚ →+* ℂ) (x : ↥(ModularCurve.modularFunctionFieldBar N))
    (h₁ : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({ModularCurve.jBar N} : Set ↥(ModularCurve.modularFunctionFieldBar N)))
      (x ^ 6 * ModularCurve.jBar N ^ (4 * m) *
        (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (3 * m)))
    (h₂ : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(ModularCurve.jBar N)⁻¹} : Set ↥(ModularCurve.modularFunctionFieldBar N)))
      (x ^ (2 * ModularCurve.dedekindPsi N) * ModularCurve.jBar N ^ (m * ModularCurve.dedekindPsi N + 1) *
        (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (m * ModularCurve.dedekindPsi N))) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ)),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 f) =
        ModularCurve.coeffMap ι₀ ((x : ↥(ModularCurve.modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) *
          ModularCurve.thetaL ℂ (ModularCurve.coeffEmb ℂ ModularCurve.jq) ^ m := by sorry
