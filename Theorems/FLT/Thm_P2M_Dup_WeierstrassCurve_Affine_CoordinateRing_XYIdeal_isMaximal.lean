import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate
theorem P2M.Dup.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal {K : Type*} [Field K] {W : Affine K} {a b : K} (h : W.Equation a b) : (XYIdeal W a (C b)).IsMaximal := by sorry
