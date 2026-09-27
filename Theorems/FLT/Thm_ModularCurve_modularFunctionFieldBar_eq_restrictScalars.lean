import Definitions.FLT.Def_ModularCurve_AtkinLehner
import Definitions.FLT.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.modularFunctionFieldBar_eq_restrictScalars (ℓ : ℕ) [Fact ℓ.Prime] : modularFunctionFieldBar ℓ = (IntermediateField.adjoin (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ)))) ({jqNModC (AlgebraicClosure ℚ) ℓ} : Set (LaurentSeries (AlgebraicClosure ℚ)))).restrictScalars (AlgebraicClosure ℚ) := by sorry
