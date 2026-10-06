import Definitions.FLT.Def_ModularCurve_JqCoeff
import Definitions.FLT.Def_ModularCurve_QExpansionDiff
import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm
theorem ModularCurve.exists_divisor_two_mul_eq_ord_add_weightFloor_one_laurentBaseChange_gamma1
    (M : ℕ) [NeZero M] (hM : 5 ≤ M)
    (y : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (w : ModularForm (Gamma1 M) 1) (hw : w ≠ 0)
    (v : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hv : (v : LaurentSeries ℂ) * ModularCurve.thetaL ℂ (ModularCurve.jqModC ℂ) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 w) ^ 2) :
    ∃ D : AlgebraicCurve.Divisor ℂ
        ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))),
      ∀ P : AlgebraicCurve.Place ℂ
        ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))),
        2 * D P = P.ord v +
          ((if 0 < P.ord y then (2 * P.ord y) / 3 else 0)
            + (if 0 < P.ord (y - 1728) then (P.ord (y - 1728)) / 2 else 0)
            + (if P.ord y < 0 then P.ord y else 0)) := by sorry
