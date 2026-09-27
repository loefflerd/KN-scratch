import Definitions.FLT.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.coeff_jqModC_pow_of_lt (K : Type*) [CommRing K] {b : ℕ} {m : ℤ} (hm : m < -(b : ℤ)) :
    ((jqModC K) ^ b).coeff m = 0 := by sorry
