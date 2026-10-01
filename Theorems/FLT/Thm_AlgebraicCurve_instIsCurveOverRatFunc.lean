import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.SimpleRing.Principal

import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.instIsCurveOverRatFunc (K : Type*) [Field K] :
    AlgebraicCurve.IsCurveOver K (RatFunc K) := by sorry
