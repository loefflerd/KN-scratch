import Definitions.FLT.Def_WeierstrassCurve_Velu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.velu2_secant_negAddY_cleared_identity
    {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x₁ y₁ x₂ y₂ : F}
    (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hx12 : x₁ ≠ x₂) :
    (x₂ - x₀)
          * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀)
          * (x₂ - W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
          * (y₁ - y₀)
        - (x₁ - x₀)
          * ((W.a₁ * (x₂ - x₀) + y₂ - y₀)
                * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀) ^ 2
              - (W.a₁ * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀)
                    + W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) - y₀)
                * (x₂ - x₀) ^ 2)
        + W.veluGx x₀ y₀
          * ((W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀) * (y₂ - y₀)
              - (x₂ - x₀)
                * (W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) - y₀))
      = 0 := by sorry
