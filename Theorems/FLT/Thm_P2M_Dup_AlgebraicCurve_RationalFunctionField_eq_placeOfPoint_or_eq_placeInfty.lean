import Mathlib
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.FLT.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaceClassification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem P2M.Dup.AlgebraicCurve.RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) : (∃ a : K, v = placeOfPoint K a) ∨ v = placeInfty K := by sorry
