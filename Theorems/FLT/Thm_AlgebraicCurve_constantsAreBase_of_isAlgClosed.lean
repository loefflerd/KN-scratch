import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_AdelicIndex
import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.constantsAreBase_of_isAlgClosed (K F : Type*) [Field K] [Field F] [Algebra K F]
    [DecidableEq (RatFunc K)] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
    [IsAlgClosed K] [AlgebraicCurve.IsCurveOver K F] :
    AlgebraicCurve.ConstantsAreBase K F := by sorry
