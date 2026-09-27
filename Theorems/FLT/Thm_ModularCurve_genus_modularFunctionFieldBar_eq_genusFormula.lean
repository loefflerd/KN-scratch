import Mathlib
import Definitions.FLT.Def_ModularCurve_ArithmeticGalois
import Definitions.FLT.Def_ModularCurve_GenusNumerics
import Definitions.FLT.Def_AlgebraicCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula (N : ℕ) [NeZero N]
    [AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.modularFunctionFieldBar N))] :
    (AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℚ)
      = ModularCurve.genusFormula N := by sorry
