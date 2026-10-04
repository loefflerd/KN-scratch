import Definitions.FLT.Def_ModularCurve_ModularUnit
import Definitions.FLT.Def_ModularCurve_QExpansionDiff
import Definitions.FLT.Def_ModularCurve_TateFormal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.thetaL_jq_mul_deltaSeries :
    thetaL ℚ jq * deltaSeries =
      -(HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) (eisenstein4 ^ 2 * eisenstein6))) := by sorry
