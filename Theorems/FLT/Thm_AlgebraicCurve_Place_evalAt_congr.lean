import Definitions.FLT.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.Place.evalAt_congr {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) (h : f - g = 0 ∨ 0 < v.ord (f - g)) : v.evalAt f = v.evalAt g := by sorry
