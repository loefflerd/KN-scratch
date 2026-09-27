import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.FLT.Def_AlgebraicCurve_Repartitions
import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver
import Definitions.FLT.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve
theorem finiteDimensional_lSpace {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [hL0 : FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    (D : Divisor K F) : FiniteDimensional K ↥(LSpace D) := by sorry
