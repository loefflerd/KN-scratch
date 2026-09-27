import Definitions.FLT.Def_ModularCurve_CuspidalClass
import Theorems.FLT.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_cuspZeroBar_coeffEmb_jq

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) :
    (cuspZeroBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = -N := by
  have e := ModularCurve.ord_cuspZeroBar_coeffEmb_qExpand N h N 1 (mul_one N)
  have hj : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro_left N (mul_one N)))⟩ : modularFunctionFieldBar N) =
      ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :=
    Subtype.ext (by simp only [qExpand_one_apply])
  rwa [hj] at e

end S_ModularCurve_ord_cuspZeroBar_coeffEmb_jq
end P2MW
export P2MW.S_ModularCurve_ord_cuspZeroBar_coeffEmb_jq (solution)
