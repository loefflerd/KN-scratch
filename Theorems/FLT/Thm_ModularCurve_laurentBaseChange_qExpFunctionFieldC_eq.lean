import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
open ModularCurve
theorem ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq
    (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ)) :
    ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ) = ModularCurve.qExpFunctionFieldC L Γ := by sorry
