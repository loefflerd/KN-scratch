import Definitions.FLT.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.FLT.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve
theorem ModularCurve.hasCanonicalDivisor_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N) := by sorry
