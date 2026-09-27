import Definitions.FLT.Def_ModularCurve_ArithmeticGalois
import Definitions.FLT.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.functionFieldRiemannRoch_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    FunctionFieldRiemannRoch (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by sorry
