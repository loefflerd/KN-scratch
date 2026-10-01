import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem AlgebraicCurve.RationalFunctionField.ord_placeOfPoint_algebraMap {K : Type*} [Field K] (a : K) {q : Polynomial K} (hq : q ≠ 0) : (placeOfPoint K a).ord (algebraMap (Polynomial K) (RatFunc K) q) = Polynomial.rootMultiplicity a q := by sorry
