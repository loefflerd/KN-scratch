import Definitions.FLT.Def_ModularCurve_AtkinLehner
import Definitions.FLT.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve IntermediateField
theorem ModularCurve.exists_isFrickeAut_of_modularPolynomialData {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data) : ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ := by sorry
