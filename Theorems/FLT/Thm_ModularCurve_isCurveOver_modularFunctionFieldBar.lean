import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver
import Definitions.FLT.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve
theorem ModularCurve.isCurveOver_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by sorry
