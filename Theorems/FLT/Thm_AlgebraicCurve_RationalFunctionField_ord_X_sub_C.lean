import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem AlgebraicCurve.RationalFunctionField.ord_X_sub_C (K : Type*) [Field K] [DecidableEq (RatFunc K)] (b : K) (v : Place K (RatFunc K)) : v.ord (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C b)) = (Finsupp.single (placeOfPoint K b) (1 : ℤ) + Finsupp.single (placeInfty K) (-1 : ℤ)) v := by sorry
