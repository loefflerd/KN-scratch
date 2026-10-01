import Definitions.FLT.Def_AlgebraicCurve_AdelicIndex
import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve
theorem stichtenothGenusExists_of_isCurveOver {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    StichtenothGenusExists K F := by sorry
