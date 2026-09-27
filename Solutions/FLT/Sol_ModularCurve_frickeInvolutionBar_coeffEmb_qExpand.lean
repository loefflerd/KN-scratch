import Definitions.FLT.Def_ModularCurve_CuspidalClass
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (a b : ℕ) (hab : a * b = N) [NeZero a] [NeZero b] :
    frickeInvolutionBar N ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro b hab))⟩ = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro_left a hab))⟩ := by
  rw [frickeInvolutionBar_def]
  refine (geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N)
    ⟨qExpand ℚ a jq, jqd_mem_full N (Dvd.intro b hab)⟩).trans (Subtype.ext ?_)
  change coeffEmb (AlgebraicClosure ℚ) ((frickeInvolutionFull N ⟨qExpand ℚ a jq, _⟩ : modularFunctionFieldFull N) :
    LaurentSeries ℚ) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq)
  rw [h a b hab ‹NeZero a› ‹NeZero b›]

end S_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
end P2MW
export P2MW.S_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand (solution)
