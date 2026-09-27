import Definitions.FLT.Def_ModularCurve_QAdicPlace
import Definitions.FLT.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.transcendental_coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] : Transcendental L (⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩ : laurentBaseChange L (modularFunctionFieldFull N)) := by sorry
