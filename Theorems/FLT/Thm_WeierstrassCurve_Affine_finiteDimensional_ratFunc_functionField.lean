import Definitions.FLT.Def_WeierstrassCurve_FunctionFieldQuadratic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.Affine.finiteDimensional_ratFunc_functionField {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) :
    FiniteDimensional (RatFunc F) W.FunctionField := by sorry
