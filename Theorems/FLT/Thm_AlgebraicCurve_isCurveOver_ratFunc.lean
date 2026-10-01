import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.SimpleRing.Principal

import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.isCurveOver_ratFunc (K : Type*) [Field K] :
    IsCurveOver K (RatFunc K) := by sorry
