import Definitions.FLT.Def_WeierstrassCurve_VeluPointMap2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    ∃ φ : W.toAffine.Point →+ (W.veluQuotient2 x₀ y₀).toAffine.Point,
      ⇑φ = veluPointMap2 h2 hQ hgy hΔ := by sorry
