import Mathlib.Basic.Complex.Basic

import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem HeckeEis.finrank_coeffH1par_zero_le_two_mul_genusFormula (N : ℕ) [NeZero N] :
    (Module.finrank ℂ (HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ 0).comp (CongruenceSubgroup.Gamma0 N).subtype)) : ℚ)
      ≤ 2 * ModularCurve.genusFormula N := by sorry
