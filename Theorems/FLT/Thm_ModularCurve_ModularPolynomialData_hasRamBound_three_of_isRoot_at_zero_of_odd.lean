import Definitions.FLT.Def_HahnSeries_RamificationBound
import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.ModularPolynomialData.hasRamBound_three_of_isRoot_at_zero_of_odd
    {N : ℕ} [NeZero N] (hN : Odd N) (data : ModularCurve.ModularPolynomialData N)
    (r : HahnSeries ℚ (AlgebraicClosure ℚ))
    (hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
      (HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)))).IsRoot r) :
    HahnSeries.HasRamBound 3 r := by sorry
