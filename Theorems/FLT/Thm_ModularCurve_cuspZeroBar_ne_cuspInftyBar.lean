module

public import Definitions.FLT.Def_ModularCurve_CuspidalClass

import Theorems.FLT.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq
import Theorems.FLT.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_cuspZeroBar_ne_cuspInftyBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (hN : 1 < N) :
    cuspZeroBar N ≠ cuspInftyBar N := by
  intro e
  have h0 := ModularCurve.ord_cuspZeroBar_coeffEmb_jq N h
  rw [e, ModularCurve.ord_cuspInftyBar_coeffEmb_jq] at h0
  have : (N : ℤ) = 1 := by linarith
  exact absurd (Nat.cast_eq_one.mp this) hN.ne'

end S_ModularCurve_cuspZeroBar_ne_cuspInftyBar
end P2MW
export P2MW.S_ModularCurve_cuspZeroBar_ne_cuspInftyBar (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.cuspZeroBar_ne_cuspInftyBar (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (hN : 1 < N) : cuspZeroBar N ≠ cuspInftyBar N := _root_.P2MW.S_ModularCurve_cuspZeroBar_ne_cuspInftyBar.solution N h hN

end publicSection
