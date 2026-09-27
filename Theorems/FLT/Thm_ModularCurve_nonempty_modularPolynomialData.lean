import Mathlib
import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.nonempty_modularPolynomialData (N : ℕ) [NeZero N] :
    Nonempty (ModularCurve.ModularPolynomialData N) := by sorry
