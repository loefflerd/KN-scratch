module

public import Definitions.FLT.Def_ModularCurve_LaurentCoeff

import Theorems.FLT.Thm_ModularCurve_coeffMap_injective
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffEmb_injective

open ModularCurve IntermediateField HahnSeries

theorem solution (L : Type*) [Field L] [Algebra ℚ L] : Function.Injective (ModularCurve.coeffEmb L) :=
  coeffMap_injective (FaithfulSMul.algebraMap_injective ℚ L)

end S_ModularCurve_coeffEmb_injective
end P2MW
export P2MW.S_ModularCurve_coeffEmb_injective (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.coeffEmb_injective (L : Type*) [Field L] [Algebra ℚ L] : Function.Injective (ModularCurve.coeffEmb L) := _root_.P2MW.S_ModularCurve_coeffEmb_injective.solution L

end publicSection
