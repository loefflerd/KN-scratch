import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare (N : ℕ) [NeZero N] (hN : ¬ IsSquare N) (data : ModularCurve.ModularPolynomialData N) : IsUnit (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff := by sorry
