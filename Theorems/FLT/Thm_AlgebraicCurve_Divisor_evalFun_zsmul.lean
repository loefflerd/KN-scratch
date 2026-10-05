module

public import Definitions.FLT.Def_AlgebraicCurve_PlaceEvaluation

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_zsmul

open AlgebraicCurve AlgebraicCurve.Divisor

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) (D : Divisor K F) (n : ℤ) : Divisor.evalFun f (n • D) = Divisor.evalFun f D ^ n := by
  rw [show evalFun f (n • D) = ∏ v ∈ D.support, v.evalAt f ^ ((n • D) v) from
      Finsupp.prod_of_support_subset _ Finsupp.support_smul _ fun v _ => zpow_zero _,
    evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm n (D v), zpow_mul]

end S_AlgebraicCurve_Divisor_evalFun_zsmul
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_evalFun_zsmul (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_zsmul {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) (D : Divisor K F) (n : ℤ) : Divisor.evalFun f (n • D) = Divisor.evalFun f D ^ n := _root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_zsmul.solution f D n

end publicSection
