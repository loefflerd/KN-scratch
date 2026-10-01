import Definitions.FLT.Def_ModularCurve_LevelNFunctionField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
theorem ModularCurve.LevelN.isDomain_ring (M : ℕ) [NeZero M] : IsDomain (ModularCurve.LevelN.ring M) := by sorry
