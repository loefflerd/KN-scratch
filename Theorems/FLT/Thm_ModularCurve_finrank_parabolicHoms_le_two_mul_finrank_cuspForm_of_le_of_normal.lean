import Mathlib.NumberTheory.ModularForms.Basic

import Definitions.FLT.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal
    (Γ' Γ : Subgroup SL(2, ℤ)) [Γ'.FiniteIndex] (hle : Γ' ≤ Γ) (hn : (Γ'.subgroupOf Γ).Normal)
    (h : Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ' ℤ) ≤
      2 * Module.finrank ℂ (CuspForm Γ' 2)) :
    Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ) ≤
      2 * Module.finrank ℂ (CuspForm Γ 2) := by sorry
