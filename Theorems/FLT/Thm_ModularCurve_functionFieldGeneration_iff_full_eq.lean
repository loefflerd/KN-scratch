module

public import Definitions.FLT.Def_ModularCurve_X0

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_functionFieldGeneration_iff_full_eq

open ModularCurve IntermediateField

noncomputable section

theorem solution (N : ℕ) [NeZero N] : FunctionFieldGeneration N ↔ modularFunctionFieldFull N = modularFunctionField N :=by
  constructor
  · intro hgen
    refine le_antisymm ?_ (modularFunctionField_le_full N)
    rw [modularFunctionFieldFull, adjoin_le_iff]
    rintro x ⟨d, hne, hdvd, rfl⟩
    exact hgen d hdvd hne
  · intro heq d hdvd hne
    have := hne
    show qExpand ℚ d jq ∈ modularFunctionField N
    rw [← heq]
    exact jqd_mem_full N hdvd

end

end S_ModularCurve_functionFieldGeneration_iff_full_eq
end P2MW
export P2MW.S_ModularCurve_functionFieldGeneration_iff_full_eq (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve IntermediateField
theorem ModularCurve.functionFieldGeneration_iff_full_eq (N : ℕ) [NeZero N] : FunctionFieldGeneration N ↔ modularFunctionFieldFull N = modularFunctionField N := _root_.P2MW.S_ModularCurve_functionFieldGeneration_iff_full_eq.solution N

end publicSection
