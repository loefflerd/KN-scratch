import Mathlib.NumberTheory.ModularForms.Basic

import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.genusFormula_le_finrank_gamma0_weight_two (N : ℕ) [NeZero N] :
    ModularCurve.genusFormula N ≤ (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) : ℚ) := by sorry
