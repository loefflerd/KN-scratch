import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.ModularPolynomialData.eq_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)] (d d' : ModularPolynomialData p) : d = d' := by sorry
