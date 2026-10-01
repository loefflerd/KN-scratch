import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

import Definitions.FLT.Def_WeierstrassCurve_FunctionFieldQuadratic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.Affine.adjoin_yCoord_eq_top {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} :
    IntermediateField.adjoin (RatFunc F) {WeierstrassCurve.Affine.yCoord W} = ⊤ := by sorry
