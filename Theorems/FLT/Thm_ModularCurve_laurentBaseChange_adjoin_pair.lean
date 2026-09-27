import Definitions.FLT.Def_ModularCurve_DegeneracyTower
import Definitions.FLT.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.laurentBaseChange_adjoin_pair (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M] (hgenQ : FunctionFieldGeneration M) : laurentBaseChange L (modularFunctionFieldFull M) = IntermediateField.adjoin L {jqModC L, jqNModC L M} := by sorry
