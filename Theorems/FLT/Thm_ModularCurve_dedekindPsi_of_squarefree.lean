import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.dedekindPsi_of_squarefree {N : ℕ} (hN : Squarefree N) : dedekindPsi N = ∏ p ∈ N.primeFactors, (p + 1) := by sorry
