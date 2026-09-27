import Definitions.FLT.Def_ModularCurve_QAdicPlace
import Definitions.FLT.Def_ModularCurve_LaurentCoeff
import Mathlib.FieldTheory.Relrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.relfinrank_laurentBaseChange_modularFunctionFieldFull (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] : IntermediateField.relfinrank (IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))) (laurentBaseChange L (modularFunctionFieldFull N)) = IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularFunctionFieldFull N) := by sorry
