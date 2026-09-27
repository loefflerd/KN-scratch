import Mathlib
import Definitions.FLT.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.essFiniteType_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) := by sorry
