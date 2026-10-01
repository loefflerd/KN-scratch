import Definitions.FLT.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.FLT.Def_AlgebraicCurve_Repartitions
import Definitions.FLT.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.genus_eq_genusFF_modularFunctionFieldBar (N : ℕ) [NeZero N]
    [AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.modularFunctionFieldBar N))] :
    AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N)
      = AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) := by sorry
