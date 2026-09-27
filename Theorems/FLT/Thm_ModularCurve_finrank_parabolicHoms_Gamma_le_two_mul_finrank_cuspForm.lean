import Mathlib
import Definitions.FLT.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem ModularCurve.finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm (N : ℕ) [NeZero N] :
    Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma N) ℤ) ≤
      2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) := by sorry
