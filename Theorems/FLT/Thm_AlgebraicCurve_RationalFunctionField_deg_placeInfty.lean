import Mathlib
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.FLT.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem AlgebraicCurve.RationalFunctionField.deg_placeInfty (K : Type*) [Field K] [DecidableEq (RatFunc K)] : (placeInfty K).deg = 1 := by sorry
