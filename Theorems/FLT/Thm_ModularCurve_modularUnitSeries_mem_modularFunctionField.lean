import Definitions.FLT.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.modularUnitSeries_mem_modularFunctionField (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : ModularCurve.modularUnitSeries ℓ ∈ ModularCurve.modularFunctionField ℓ := by sorry
