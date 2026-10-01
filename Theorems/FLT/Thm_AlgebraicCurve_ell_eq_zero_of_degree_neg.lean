import Definitions.FLT.Def_AlgebraicCurve_AdelicIndex
import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve
theorem ell_eq_zero_of_degree_neg {K F : Type*} [Field K] [Field F] [Algebra K F] {D : Divisor K F} [IsCurveOver K F] (hD : Divisor.degree D < 0) :
    ell D = 0 := by sorry
