import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

import Definitions.FLT.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem ModularCurve.six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq (N : ℕ) (hN : 2 ≤ N) :
    6 * N * Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma N) ℤ) +
        6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      12 * N + N * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by sorry
