import Mathlib
import Definitions.FLT.Def_ModularCurve_X1
import Definitions.FLT.Def_ModularCurve_IgusaFunctionFieldX1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
theorem ModularCurve.nonempty_integralWeightOneForm
    (κ : Type) [Field κ] (M : ℕ) (hM : 3 ≤ M) :
    Nonempty (ModularCurve.IntegralWeightOneForm κ M) := by sorry
