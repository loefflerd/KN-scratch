import Definitions.FLT.Def_ModularCurve_EMD
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve IsDedekindDomain WithZero
theorem ModularCurve.place_eq_of_induces {N : ℕ} [NeZero N]
    {ψ : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ] HahnSeries ℚ (AlgebraicClosure ℚ)}
    {w w' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)}
    (h : Induces ψ w) (h' : Induces ψ w') : w = w' := by sorry
