import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.FLT.Def_WeierstrassCurve_Velu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine
theorem ModularCurve.ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    (n : ℕ) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) :
    haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) W.j)).IsRoot
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j := by sorry
