import Definitions.FLT.Def_ModularCurve_HeckeDifferential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.diffQExpBar_injective_of_neZero (N : ℕ) [NeZero N] :
    Function.Injective (diffQExpBar N) := by sorry
