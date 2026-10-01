import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

import Definitions.FLT.Def_ModularCurve_GenusNumerics
import Definitions.FLT.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.finrank_parabolicHoms_le_two_mul_genusFormula (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [CharZero K] :
    (Module.finrank K (ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 N) K) : ℚ) ≤
      2 * ModularCurve.genusFormula N := by sorry
