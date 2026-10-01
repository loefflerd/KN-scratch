import Definitions.FLT.Def_WeierstrassCurve_Velu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.velu2_tangent_negAddY_cleared_identity
    {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hy : y ≠ W.toAffine.negY x y) :
    (x - x₀) * (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀)
          * (x - W.toAffine.addX x x (W.toAffine.slope x x y y)) * (y - y₀)
        - (x - x₀)
          * ((W.a₁ * (x - x₀) + y - y₀)
                * (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀) ^ 2
              - (W.a₁ * (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀)
                    + W.toAffine.negAddY x x y (W.toAffine.slope x x y y) - y₀)
                * (x - x₀) ^ 2)
        + W.veluGx x₀ y₀
          * ((W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀) * (y - y₀)
              - (x - x₀) * (W.toAffine.negAddY x x y (W.toAffine.slope x x y y) - y₀))
      = 0 := by sorry
