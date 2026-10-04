import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

import Theorems.FLT.Thm_WeierstrassCurve_Affine_adjoin_yCoord_eq_top
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_finiteDimensional_ratFunc_functionField

set_option synthInstance.maxHeartbeats 800000

open WeierstrassCurve.Affine in
theorem solution {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) :
    FiniteDimensional (RatFunc F) W.FunctionField := by
  have h1 : FiniteDimensional (RatFunc F)
      (IntermediateField.adjoin (RatFunc F) {yCoord W}) :=
    IntermediateField.adjoin.finiteDimensional isIntegral_yCoord
  rw [WeierstrassCurve.Affine.adjoin_yCoord_eq_top] at h1
  exact (IntermediateField.topEquiv
    (F := RatFunc F) (E := W.FunctionField)).toLinearEquiv.finiteDimensional

end S_WeierstrassCurve_Affine_finiteDimensional_ratFunc_functionField
end P2MW
export P2MW.S_WeierstrassCurve_Affine_finiteDimensional_ratFunc_functionField (solution)
