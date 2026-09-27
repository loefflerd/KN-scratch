import Definitions.FLT.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.Place.evalAt_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by sorry
