import Definitions.FLT.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional (L : Type*) [Field L] [Algebra ℚ L]
    (N : ℕ) [NeZero N] : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull N)) := by sorry
