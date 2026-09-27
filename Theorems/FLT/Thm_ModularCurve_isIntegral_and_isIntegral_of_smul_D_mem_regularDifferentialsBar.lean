import Mathlib
import Definitions.FLT.Def_ModularCurve_HeckeDifferential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentialsBar (N : ℕ) [NeZero N]
    (x : ModularCurve.modularFunctionFieldBar N)
    (hx : x • KaehlerDifferential.D (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N)
        (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ : ModularCurve.modularFunctionFieldBar N) ∈ ModularCurve.regularDifferentialsBar N) :
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ : ModularCurve.modularFunctionFieldBar N)} : Set (ModularCurve.modularFunctionFieldBar N)))
        (x ^ 6 * (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ : ModularCurve.modularFunctionFieldBar N) ^ 4 * ((⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ : ModularCurve.modularFunctionFieldBar N) - algebraMap (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) 1728) ^ 3) ∧
      IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ : ModularCurve.modularFunctionFieldBar N)⁻¹} : Set (ModularCurve.modularFunctionFieldBar N)))
        (x ^ (2 * ModularCurve.dedekindPsi N) * (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ : ModularCurve.modularFunctionFieldBar N) ^ (ModularCurve.dedekindPsi N + 1) *
          ((⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ : ModularCurve.modularFunctionFieldBar N) - algebraMap (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) 1728) ^ ModularCurve.dedekindPsi N) := by sorry
