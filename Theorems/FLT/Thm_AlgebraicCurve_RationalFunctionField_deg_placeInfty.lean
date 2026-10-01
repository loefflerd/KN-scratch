import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem AlgebraicCurve.RationalFunctionField.deg_placeInfty (K : Type*) [Field K] [DecidableEq (RatFunc K)] : (placeInfty K).deg = 1 := by sorry
