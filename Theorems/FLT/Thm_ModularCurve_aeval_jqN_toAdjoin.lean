import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.aeval_jqN_toAdjoin {N : ℕ} [NeZero N] (data : ModularPolynomialData N) : Polynomial.aeval (jqN N) data.toAdjoin = 0 := by sorry
