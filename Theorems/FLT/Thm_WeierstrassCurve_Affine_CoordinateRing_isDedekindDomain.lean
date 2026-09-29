import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate
theorem WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain {K : Type*} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic] : IsDedekindDomain W.toAffine.CoordinateRing := by sorry
