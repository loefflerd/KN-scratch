import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve
theorem RationalFunctionField.ord_placeInfty_X (K : Type*) [Field K] [DecidableEq (RatFunc K)] : (RationalFunctionField.placeInfty K).ord (RatFunc.X : RatFunc K) = -1 := by sorry
