import Definitions.FLT.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.eq_cuspInftyBar_or_eq_cuspZeroBar (ℓ : ℕ) [Fact ℓ.Prime] (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar ℓ)) (hc : IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full ℓ)⟩ : modularFunctionFieldBar ℓ) w) : w = cuspInftyBar ℓ ∨ w = cuspZeroBar ℓ := by sorry
