import Definitions.FLT.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve
theorem RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase (K : Type*) [Field K] (F : Type*) [Field F] [Algebra K F] (hC : ConstantsAreBase K F) :
    FiniteDimensional K (LSpace (0 : Divisor K F)) := by sorry
