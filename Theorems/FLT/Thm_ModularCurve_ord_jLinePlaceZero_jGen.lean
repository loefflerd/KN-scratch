import Definitions.FLT.Def_ModularCurve_JLinePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve
theorem ModularCurve.ord_jLinePlaceZero_jGen : ModularCurve.jLinePlaceZero.ord ModularCurve.jGen = 1 := by sorry
