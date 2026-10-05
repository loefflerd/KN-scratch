import Definitions.FLT.Def_ModularCurve_JqCoeff
import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.jqModC_mem_intFormRatiosC (K : Type*) [Field K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    ModularCurve.jqModC K ∈ ModularCurve.intFormRatiosC K Γ := by sorry
