import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.RationalFunctionField.finite_setOf_ord_ne_zero {K : Type*} [Field K] {f : RatFunc K} (hf : f ≠ 0) : {v : Place K (RatFunc K) | v.ord f ≠ 0}.Finite := by sorry
