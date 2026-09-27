import Definitions.FLT.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.normFormulaAlong {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [CharZero F] (φ : F →ₐ[K] F') [HasPrincipalDivisors K F'] (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) : NormFormulaAlong K φ hfin := by sorry
