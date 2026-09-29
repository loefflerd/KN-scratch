import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u
theorem WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange
    {F : Type u} [Field F] (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F) :
    Nonempty (W.toAffine.FunctionField ≃ₐ[F] (C • W).toAffine.FunctionField) := by sorry
