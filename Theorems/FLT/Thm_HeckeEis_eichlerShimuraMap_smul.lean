import Mathlib.NumberTheory.ModularForms.Basic

import Definitions.FLT.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm
theorem HeckeEis.eichlerShimuraMap_smul (n N : ℕ) [NeZero N] (c : ℂ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    HeckeEis.eichlerShimuraMap n N ⇑(c • f) = c • HeckeEis.eichlerShimuraMap n N f := by sorry
