import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_isMaximal

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

theorem solution {K : Type*} [Field K] {W : Affine K} {a b : K} (h : W.Equation a b) : (XYIdeal W a (C b)).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ <|
    MulEquiv.isField (Field.toIsField K) (quotientXYIdealEquiv (W' := W) h).toMulEquiv

end S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_isMaximal
end P2MW
export P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_isMaximal (solution)
