import Definitions.FLT.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_of_neZero (M : ℕ) [NeZero M] :
    FiniteDimensional
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full M)⟩}
          : Set (modularFunctionFieldBar M)))
      (modularFunctionFieldBar M) := by sorry
