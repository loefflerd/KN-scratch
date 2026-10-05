module

public import Definitions.FLT.Def_ModularCurve_X0

import Theorems.FLT.Thm_ModularCurve_PhiGen_evalAtJ_injective
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_evalAtJGen_injective

open ModularCurve IntermediateField

theorem solution :
    Function.Injective (ModularCurve.evalAtJGen : Polynomial ℤ →+* ↥ℚ⟮ModularCurve.jq⟯) := by
  intro a b hab
  apply ModularCurve.PhiGen.evalAtJ_injective
  rw [← ModularCurve.algebraMap_comp_evalAtJGen, RingHom.comp_apply, RingHom.comp_apply, hab]

end S_ModularCurve_evalAtJGen_injective
end P2MW
export P2MW.S_ModularCurve_evalAtJGen_injective (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve IntermediateField
theorem ModularCurve.evalAtJGen_injective :
    Function.Injective (ModularCurve.evalAtJGen : Polynomial ℤ →+* ↥ℚ⟮ModularCurve.jq⟯) := _root_.P2MW.S_ModularCurve_evalAtJGen_injective.solution

end publicSection
