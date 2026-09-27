import Definitions.FLT.Def_ModularCurve_ProjectiveLine
import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.card_projectiveLine_zmod (N : ℕ) (hN : N ≠ 0) : Nat.card (ProjectiveLine (ZMod N)) = dedekindPsi N := by sorry
