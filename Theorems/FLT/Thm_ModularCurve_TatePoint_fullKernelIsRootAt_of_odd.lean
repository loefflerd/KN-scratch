import Definitions.FLT.Def_ModularCurve_CycSubRootBridgeN

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Classical
theorem ModularCurve.TatePoint.fullKernelIsRootAt_of_odd (N : ℕ) [NeZero N] (hN : Odd N) : FullKernelIsRootAt N := by sorry
