module

public import Definitions.FLT.Def_ModularCurve_LaurentCoeff
public import Definitions.FLT.Def_ModularCurve_X0

import Theorems.FLT.Thm_ModularCurve_coeffMap_qExpand
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffEmb_qExpand

open ModularCurve IntermediateField HahnSeries

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) : ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ n x) = ModularCurve.qExpand L n (ModularCurve.coeffEmb L x) :=
  coeffMap_qExpand _ n x

end S_ModularCurve_coeffEmb_qExpand
end P2MW
export P2MW.S_ModularCurve_coeffEmb_qExpand (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) : ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ n x) = ModularCurve.qExpand L n (ModularCurve.coeffEmb L x) := _root_.P2MW.S_ModularCurve_coeffEmb_qExpand.solution L n x

end publicSection
