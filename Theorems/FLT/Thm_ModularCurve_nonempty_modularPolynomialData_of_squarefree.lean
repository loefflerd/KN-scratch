import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.nonempty_modularPolynomialData_of_squarefree (N : ℕ) [NeZero N] (hsf : Squarefree N) (hN : 1 < N) : Nonempty (ModularPolynomialData N) := by sorry
