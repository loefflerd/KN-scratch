import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver
import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve CongruenceSubgroup AlgebraicCurve
open scoped MatrixGroups
theorem ModularCurve.isCurveOver_laurentBaseChange_qExpFunctionFieldC_gamma1
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K] (M : ℕ) [NeZero M] :
    AlgebraicCurve.IsCurveOver K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) := by sorry
