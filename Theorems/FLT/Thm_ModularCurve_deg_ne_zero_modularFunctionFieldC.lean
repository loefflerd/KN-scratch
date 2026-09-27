import Definitions.FLT.Def_ModularCurve_JqCoeff
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve
theorem ModularCurve.deg_ne_zero_modularFunctionFieldC (K : Type*) [Field K] (N : ℕ) [NeZero N] (w : Place K (modularFunctionFieldC K N)) : w.deg ≠ 0 := by sorry
