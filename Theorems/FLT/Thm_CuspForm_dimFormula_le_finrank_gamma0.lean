import Mathlib.NumberTheory.ModularForms.Basic

import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.dimFormula_le_finrank_gamma0 (N : ℕ) [NeZero N] (k : ℕ) (hk : 4 ≤ k) (hke : Even k) :
    (((k : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + ((k / 4 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ)
        + ((k / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + ((k : ℚ) / 2 - 1) * (ModularCurve.cuspCount N : ℚ))
      ≤ (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) (k : ℤ)) : ℚ) := by sorry
