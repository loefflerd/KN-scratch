module

public import Definitions.FLT.Def_ModularCurve_AtkinLehner

import Theorems.FLT.Thm_ModularCurve_ord_cuspInftyBar
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_cuspInftyBar_coeffEmb_jq

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] :
    (cuspInftyBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = -1 := by
  rw [ModularCurve.ord_cuspInftyBar]
  exact order_coeffEmb_jq (AlgebraicClosure ℚ)

end S_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
end P2MW
export P2MW.S_ModularCurve_ord_cuspInftyBar_coeffEmb_jq (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.ord_cuspInftyBar_coeffEmb_jq (N : ℕ) [NeZero N] : (cuspInftyBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = -1 := _root_.P2MW.S_ModularCurve_ord_cuspInftyBar_coeffEmb_jq.solution N

end publicSection
