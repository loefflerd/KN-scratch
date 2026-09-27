import Definitions.FLT.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.coeff_jqModC_neg_one (K : Type*) [CommRing K] :
    (jqModC K).coeff (-1 : ℤ) = 1 := by sorry
