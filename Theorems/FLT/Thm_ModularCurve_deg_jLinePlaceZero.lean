module

public import Definitions.FLT.Def_ModularCurve_JLinePlaces

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_deg_jLinePlaceZero

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial
attribute [local instance] ModularCurve.instDecidableEqRatFuncRat

theorem solution : ModularCurve.jLinePlaceZero.deg = 1 := by
  unfold ModularCurve.jLinePlaceZero
  rw [Place.deg_congrRingEquiv]
  exact deg_placeOfPoint ℚ 0

end S_ModularCurve_deg_jLinePlaceZero
end P2MW
export P2MW.S_ModularCurve_deg_jLinePlaceZero (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve
theorem ModularCurve.deg_jLinePlaceZero : ModularCurve.jLinePlaceZero.deg = 1 := _root_.P2MW.S_ModularCurve_deg_jLinePlaceZero.solution

end publicSection
