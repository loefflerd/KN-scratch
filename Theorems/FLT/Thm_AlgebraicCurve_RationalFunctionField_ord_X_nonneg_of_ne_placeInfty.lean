import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve
theorem RationalFunctionField.ord_X_nonneg_of_ne_placeInfty (K : Type*) [Field K] [DecidableEq (RatFunc K)]
    {u : Place K (RatFunc K)} (hu : u ≠ RationalFunctionField.placeInfty K) :
    0 ≤ u.ord (RatFunc.X : RatFunc K) := by sorry
