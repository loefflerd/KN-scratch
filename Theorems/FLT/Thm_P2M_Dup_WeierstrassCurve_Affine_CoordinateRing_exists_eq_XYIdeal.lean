import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate
theorem P2M.Dup.WeierstrassCurve.Affine.CoordinateRing.exists_eq_XYIdeal {K : Type*} [Field K] {W : Affine K} [IsAlgClosed K] {P : Ideal W.CoordinateRing} (hP : P ≠ ⊥) [P.IsPrime] : ∃ a b : K, W.Equation a b ∧ P = XYIdeal W a (C b) := by sorry
