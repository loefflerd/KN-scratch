import Definitions.FLT.Def_ModularCurve_LaurentCoeff
import Definitions.FLT.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] : FiniteDimensional (IntermediateField.adjoin L ({⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩} : Set (laurentBaseChange L (modularFunctionFieldFull N)))) (laurentBaseChange L (modularFunctionFieldFull N)) := by sorry
