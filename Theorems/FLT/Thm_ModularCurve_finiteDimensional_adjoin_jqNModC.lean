import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.finiteDimensional_adjoin_jqNModC (K : Type*) [Field K] {N : ℕ} [NeZero N] (data : ModularPolynomialData N) : FiniteDimensional (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) ({jqNModC K N} : Set (LaurentSeries K))) := by sorry
