import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate
theorem WeierstrassCurve.Affine.CoordinateRing.XYIdeal_ne_bot {R : Type*} [CommRing R] [Nontrivial R] {W : Affine R} (x : R) (y : R[X]) : XYIdeal W x y ≠ ⊥ := by sorry
