import Definitions.FLT.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.FLT.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.degree_canonicalDivisorOf_modularFunctionFieldBar (N : ℕ) [NeZero N]
    [AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.modularFunctionFieldBar N))]
    {ω : Ω[↥(ModularCurve.modularFunctionFieldBar N)⁄(AlgebraicClosure ℚ)]} (hω : ω ≠ 0) :
    (AlgebraicCurve.canonicalDivisorOf hω).degree
      = 2 * (AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℤ) - 2 := by sorry
