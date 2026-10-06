module

public import Definitions.FLT.Def_ModularCurve_AtkinLehner

import Theorems.FLT.Thm_ModularCurve_ord_cuspInftyBar
import Theorems.FLT.Thm_ModularCurve_order_coeffEmb
import Theorems.FLT.Thm_ModularCurve_order_qExpand
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (d : ℕ) [NeZero d] (hd : d ∣ N) :
    (cuspInftyBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hd)⟩ = -d := by
  rw [ModularCurve.ord_cuspInftyBar]
  change (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq)).order = _
  rw [ModularCurve.order_coeffEmb, ModularCurve.order_qExpand, order_jq, mul_neg, mul_one]

end S_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand
end P2MW
export P2MW.S_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.ord_cuspInftyBar_coeffEmb_qExpand (N : ℕ) [NeZero N] (d : ℕ) [NeZero d] (hd : d ∣ N) : (cuspInftyBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hd)⟩ = -d := _root_.P2MW.S_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand.solution N d hd

end publicSection
