import Definitions.FLT.Def_AlgebraicCurve_Differentials
import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver
import Definitions.FLT.Def_ModularCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.Place.ordDiff_eq_ordDifferential {K F : Type*} [Field K] [Field F] [Algebra K F]
    [CharZero K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ordDifferential ω := by sorry
