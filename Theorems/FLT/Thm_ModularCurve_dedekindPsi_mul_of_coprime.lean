import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.dedekindPsi_mul_of_coprime (M N : ℕ) (h : Nat.Coprime M N) : dedekindPsi (M * N) = dedekindPsi M * dedekindPsi N := by sorry
