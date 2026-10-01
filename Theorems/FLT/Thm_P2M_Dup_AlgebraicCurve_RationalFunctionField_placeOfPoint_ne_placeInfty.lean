import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem P2M.Dup.AlgebraicCurve.RationalFunctionField.placeOfPoint_ne_placeInfty (K : Type*) [Field K] [DecidableEq (RatFunc K)] (a : K) : placeOfPoint K a ≠ placeInfty K := by sorry
