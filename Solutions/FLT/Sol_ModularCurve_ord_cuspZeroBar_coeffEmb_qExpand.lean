import Definitions.FLT.Def_ModularCurve_CuspidalClass
import Theorems.FLT.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.FLT.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (a b : ℕ) (hab : a * b = N) [NeZero a] [NeZero b] :
    (cuspZeroBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro_left a hab))⟩ = -a := by
  rw [cuspZeroBar_def, ← ModularCurve.frickeInvolutionBar_coeffEmb_qExpand N h a b hab, Place.ord_smul]
  exact ModularCurve.ord_cuspInftyBar_coeffEmb_qExpand N a (Dvd.intro b hab)

end S_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand
end P2MW
export P2MW.S_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand (solution)
