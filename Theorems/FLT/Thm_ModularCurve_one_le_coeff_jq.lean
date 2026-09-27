import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.one_le_coeff_jq (n : ℕ) : (1 : ℚ) ≤ jq.coeff (n : ℤ) := by sorry
