import Definitions.FLT.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.FLT.Def_ModularCurve_CycSubRootBridgeOdd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Classical
theorem WeierstrassCurve.fullKernelQuotient_eq_veluQuotient_of_odd {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) {N : ℕ} (hN : Odd N) (hQ : addOrderOf Q = N) :
    W.fullKernelQuotient Q N = W.veluQuotient (W.oddOrderSummingSet Q ((N - 1) / 2)) := by sorry
