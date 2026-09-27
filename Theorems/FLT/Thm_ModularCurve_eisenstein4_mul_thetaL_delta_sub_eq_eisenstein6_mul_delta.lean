import Mathlib
import Definitions.FLT.Def_ModularCurve_TateFormal
import Definitions.FLT.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.eisenstein4_mul_thetaL_delta_sub_eq_eisenstein6_mul_delta :
    HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) eisenstein4) *
        thetaL ℚ (HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.X * dedekindEtaUnit)))
      - 3 * thetaL ℚ (HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) eisenstein4)) *
        HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.X * dedekindEtaUnit))
      = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) eisenstein6) *
        HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.X * dedekindEtaUnit)) := by sorry
