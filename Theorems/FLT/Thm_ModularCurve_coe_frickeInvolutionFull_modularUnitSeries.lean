import Definitions.FLT.Def_ModularCurve_ModularUnit
import Definitions.FLT.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.coe_frickeInvolutionFull_modularUnitSeries (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (hmem : ModularCurve.modularUnitSeries ℓ ∈ ModularCurve.modularFunctionFieldFull ℓ) : ((ModularCurve.frickeInvolutionFull ℓ ⟨ModularCurve.modularUnitSeries ℓ, hmem⟩ : ModularCurve.modularFunctionFieldFull ℓ) : LaurentSeries ℚ) = (ℓ : ℚ) ^ 12 • (ModularCurve.modularUnitSeries ℓ)⁻¹ := by sorry
