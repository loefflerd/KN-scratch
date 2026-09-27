import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.isIntegral_jqNModC_mul {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K)) {ℓ : ℕ} [NeZero ℓ] (data : ModularCurve.ModularPolynomialData ℓ) (d : ℕ) [NeZero d] (hd : ModularCurve.jqNModC K d ∈ F) : IsIntegral F (ModularCurve.jqNModC K (d * ℓ)) := by sorry
