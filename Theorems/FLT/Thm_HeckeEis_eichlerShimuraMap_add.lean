import Mathlib
import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm
theorem HeckeEis.eichlerShimuraMap_add (n N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    HeckeEis.eichlerShimuraMap n N ⇑(f + g) = HeckeEis.eichlerShimuraMap n N f + HeckeEis.eichlerShimuraMap n N g := by sorry
