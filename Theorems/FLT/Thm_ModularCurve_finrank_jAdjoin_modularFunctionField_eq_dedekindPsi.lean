import Definitions.FLT.Def_ModularCurve_JLinePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve
theorem ModularCurve.finrank_jAdjoin_modularFunctionField_eq_dedekindPsi (N : ℕ) [NeZero N] :
    @Module.finrank ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N) _ _
      (ModularCurve.jAdjoinAlgebra N).toModule = ModularCurve.dedekindPsi N := by sorry
