import Mathlib
import Definitions.FLT.Def_ModularCurve_MazurStepThreeInputs
import Definitions.FLT.Def_ModularCurve_GenusNumerics
import Definitions.FLT.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m) :
    ∃ D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N),
      ((D.degree : ℚ) + 1 - ModularCurve.genusFormula N =
        (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ)
          + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + ((m : ℚ) - 1) * (ModularCurve.cuspCount N : ℚ)) ∧
      ∀ x : ↥(ModularCurve.modularFunctionFieldBar N), x ∈ AlgebraicCurve.riemannRochSpace D →
        IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({ModularCurve.jBar N} : Set ↥(ModularCurve.modularFunctionFieldBar N)))
            (x ^ 6 * ModularCurve.jBar N ^ (4 * m) * (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (3 * m)) ∧
          IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(ModularCurve.jBar N)⁻¹} : Set ↥(ModularCurve.modularFunctionFieldBar N)))
            (x ^ (2 * ModularCurve.dedekindPsi N) * ModularCurve.jBar N ^ (m * ModularCurve.dedekindPsi N + 1) *
              (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (m * ModularCurve.dedekindPsi N)) := by sorry
