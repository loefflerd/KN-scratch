import Definitions.FLT.Def_ModularCurve_ArithmeticGalois
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve
theorem ModularCurve.deg_eq_one_modularFunctionFieldBar (M : ℕ) [NeZero M] (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) : w.deg = 1 := by sorry
