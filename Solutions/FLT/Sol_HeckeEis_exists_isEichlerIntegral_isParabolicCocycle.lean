import Mathlib
import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_EichlerIntegral
import Theorems.FLT.Thm_HeckeEis_exists_isEichlerIntegral
import Theorems.FLT.Thm_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral
import Theorems.FLT.Thm_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_isEichlerIntegral_isParabolicCocycle

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem solution (N n : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    ∃ F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n), HeckeEis.IsEichlerIntegral n f F ∧
      ∃ hF : HeckeEis.IsEquivariantPrimitiveWith
          ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F,
        HeckeEis.IsParabolicCocycle
          ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) hF.cocycle := by
  obtain ⟨F, hEI⟩ := HeckeEis.exists_isEichlerIntegral n (f := (f : UpperHalfPlane → ℂ)) (CuspFormClass.holo f)
  have hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F :=
    HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral hEI
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ))
  exact ⟨F, hEI, hF, HeckeEis.isParabolicCocycle_cocycle_of_isEichlerIntegral N n f hEI hF⟩

end S_HeckeEis_exists_isEichlerIntegral_isParabolicCocycle
end P2MW
export P2MW.S_HeckeEis_exists_isEichlerIntegral_isParabolicCocycle (solution)
