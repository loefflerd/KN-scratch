import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.exists_addEquiv_point_variableChange {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K) (C : VariableChange K) : ∃ e : W.toAffine.Point ≃+ (C • W).toAffine.Point, ∀ (x y : K) (h : W.toAffine.Nonsingular x y), ∃ h' : (C • W).toAffine.Nonsingular ((↑C.u⁻¹ : K) ^ 2 * (x - C.r)) ((↑C.u⁻¹ : K) ^ 3 * (y - C.s * x + (C.s * C.r - C.t))), e (WeierstrassCurve.Affine.Point.some x y h) = WeierstrassCurve.Affine.Point.some ((↑C.u⁻¹ : K) ^ 2 * (x - C.r)) ((↑C.u⁻¹ : K) ^ 3 * (y - C.s * x + (C.s * C.r - C.t))) h' := by sorry
