import Mathlib.Basic.Complex.Basic

import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem HeckeEis.finrank_coeffH1par_le_two_mul_dimFormula (N : ℕ) [NeZero N] (n : ℕ) (hn : 2 ≤ n) (hne : Even n) :
    (Module.finrank ℂ (HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)) : ℚ)
      ≤ 2 * ((((n + 2) : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + (((n + 2) / 4 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ)
        + (((n + 2) / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + (((n + 2) : ℚ) / 2 - 1) * (ModularCurve.cuspCount N : ℚ)) := by sorry
