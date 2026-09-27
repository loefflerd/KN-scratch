import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_AdelicIndex
import Definitions.FLT.Def_AlgebraicCurve_PoleDivisorPackage
import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.RationalFunctionField.stichtenothGenusExists_of_ratFunc_tower (K : Type*) [Field K]
    [DecidableEq (RatFunc K)] (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
    [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [AlgebraicCurve.IsCurveOver K F] [Nonempty (AlgebraicCurve.Place K F)]
    [FiniteDimensional K (AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K F))] :
    AlgebraicCurve.StichtenothGenusExists K F := by sorry
