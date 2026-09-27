import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.functionFieldGeneration_of_squarefree (N : ℕ) [NeZero N] (hN : Squarefree N) : FunctionFieldGeneration N := by sorry
