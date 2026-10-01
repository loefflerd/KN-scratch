import Definitions.FLT.Def_ModularCurve_CuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open OnePoint
theorem ModularCurve.CuspSpace.classification {N : ℕ} (hN : N ≠ 0) :
    ModularCurve.CuspSpace.Classification N := by sorry
