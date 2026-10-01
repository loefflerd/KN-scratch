import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.SimpleRing.Principal

import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem AlgebraicCurve.RationalFunctionField.deg_eq_one_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] (v : Place K (RatFunc K)) : v.deg = 1 := by sorry
