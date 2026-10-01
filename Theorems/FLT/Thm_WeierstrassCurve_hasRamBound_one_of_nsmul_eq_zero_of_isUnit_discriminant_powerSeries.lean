import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.HahnSeries.PowerSeries

import Definitions.FLT.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries
    (E : WeierstrassCurve (PowerSeries (AlgebraicClosure ℚ))) (hΔ : IsUnit E.Δ) {d : ℕ} (hd : 0 < d)
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))] (x y : HahnSeries ℚ (AlgebraicClosure ℚ))
    (h : (E.map (HahnSeries.ofPowerSeries ℚ (AlgebraicClosure ℚ))).toAffine.Nonsingular x y)
    (htor : d • (WeierstrassCurve.Affine.Point.some x y h :
      (E.map (HahnSeries.ofPowerSeries ℚ (AlgebraicClosure ℚ))).toAffine.Point) = 0) :
    HahnSeries.HasRamBound 1 x ∧ HahnSeries.HasRamBound 1 y := by sorry
