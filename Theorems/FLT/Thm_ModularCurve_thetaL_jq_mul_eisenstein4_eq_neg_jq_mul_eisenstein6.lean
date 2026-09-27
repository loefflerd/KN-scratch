import Mathlib
import Definitions.FLT.Def_ModularCurve_TateFormal
import Definitions.FLT.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve
theorem ModularCurve.thetaL_jq_mul_eisenstein4_eq_neg_jq_mul_eisenstein6 :
    thetaL ℚ jq * HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) eisenstein4) =
      -(jq * HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) eisenstein6)) := by sorry
