module

public import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

import Theorems.FLT.Thm_AlgebraicCurve_Pic0_mk_eq_zero_iff
import Theorems.FLT.Thm_AlgebraicCurve_Pic0_zsmul_mk
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) (m : ℤ) (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : m • Pic0.mk D = 0 := by
  rw [AlgebraicCurve.Pic0.zsmul_mk, AlgebraicCurve.Pic0.mk_eq_zero_iff]
  exact hD

end S_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.zsmul_mk_eq_zero_of_isPrincipal {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) (m : ℤ) (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : m • Pic0.mk D = 0 := _root_.P2MW.S_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal.solution D m hD

end publicSection
