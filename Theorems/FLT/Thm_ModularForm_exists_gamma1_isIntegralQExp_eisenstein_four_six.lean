import Mathlib
import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ArithmeticFunction.sigma
theorem ModularForm.exists_gamma1_isIntegralQExp_eisenstein_four_six (M : ℕ) [NeZero M] :
    ∃ (E4 : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 4)
      (E6 : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 6),
      ModularCurve.IsIntegralQExp E4 (PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)) ∧
      ModularCurve.IsIntegralQExp E6 (PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)) := by sorry
