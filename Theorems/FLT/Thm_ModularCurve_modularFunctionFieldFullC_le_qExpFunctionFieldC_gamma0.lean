import Definitions.FLT.Def_ModularCurve_X0ModL
import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
    (K : Type*) [Field K] (M : ℕ) [NeZero M] :
    ModularCurve.modularFunctionFieldFullC K M ≤
      ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) := by sorry
