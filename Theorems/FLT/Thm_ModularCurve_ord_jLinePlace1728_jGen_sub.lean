import Definitions.FLT.Def_ModularCurve_JLinePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve
theorem ModularCurve.ord_jLinePlace1728_jGen_sub : ModularCurve.jLinePlace1728.ord (ModularCurve.jGen - 1728) = 1 := by sorry
