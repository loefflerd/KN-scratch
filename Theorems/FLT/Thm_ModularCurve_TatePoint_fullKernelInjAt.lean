import Definitions.FLT.Def_ModularCurve_CycSubRootBridgeN

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Classical
theorem ModularCurve.TatePoint.fullKernelInjAt (N : ℕ) [NeZero N] : FullKernelInjAt N := by sorry
