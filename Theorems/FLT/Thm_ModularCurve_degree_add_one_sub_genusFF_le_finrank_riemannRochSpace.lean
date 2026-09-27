import Definitions.FLT.Def_ModularCurve_JZeroHeightForm
import Definitions.FLT.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve
theorem ModularCurve.degree_add_one_sub_genusFF_le_finrank_riemannRochSpace (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    D.degree + 1 - (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ)
      ≤ (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D) : ℤ) := by sorry
