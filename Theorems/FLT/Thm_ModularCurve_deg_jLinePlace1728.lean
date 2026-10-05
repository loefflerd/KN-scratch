module

public import Definitions.FLT.Def_ModularCurve_JLinePlaces

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_deg_jLinePlace1728

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial
attribute [local instance] ModularCurve.instDecidableEqRatFuncRat

theorem solution : ModularCurve.jLinePlace1728.deg = 1 := by
  unfold ModularCurve.jLinePlace1728
  rw [Place.deg_congrRingEquiv]
  exact deg_placeOfPoint ℚ 1728

end S_ModularCurve_deg_jLinePlace1728
end P2MW
export P2MW.S_ModularCurve_deg_jLinePlace1728 (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve
theorem ModularCurve.deg_jLinePlace1728 : ModularCurve.jLinePlace1728.deg = 1 := _root_.P2MW.S_ModularCurve_deg_jLinePlace1728.solution

end publicSection
