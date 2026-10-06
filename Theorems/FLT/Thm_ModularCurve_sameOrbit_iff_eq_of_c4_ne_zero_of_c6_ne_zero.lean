import Definitions.FLT.Def_ModularCurve_EMD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve WeierstrassCurve
theorem ModularCurve.sameOrbit_iff_eq_of_c4_ne_zero_of_c6_ne_zero (E₀ : WeierstrassCurve (AlgebraicClosure ℚ))
    (hc₄ : E₀.c₄ ≠ 0) (hc₆ : E₀.c₆ ≠ 0) (H H' : AddSubgroup E₀.toAffine.Point) :
    SameOrbit E₀ H H' ↔ H' = H ∧ ∃ g : E₀.toAffine.Point, H = AddSubgroup.zmultiples g := by sorry
