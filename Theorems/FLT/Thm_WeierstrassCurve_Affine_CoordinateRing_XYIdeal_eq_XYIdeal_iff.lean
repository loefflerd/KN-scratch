import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate
theorem WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_XYIdeal_iff {F : Type*} [Field F] {W : Affine F} {x₁ y₁ : F} (h : W.Equation x₁ y₁) (x₂ y₂ : F) : XYIdeal W x₁ (C y₁) = XYIdeal W x₂ (C y₂) ↔ x₁ = x₂ ∧ y₁ = y₂ := by sorry
