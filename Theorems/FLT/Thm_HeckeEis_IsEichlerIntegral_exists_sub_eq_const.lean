import Mathlib
import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm
theorem HeckeEis.IsEichlerIntegral.exists_sub_eq_const {n : ℕ} {f : UpperHalfPlane → ℂ}
    {F G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (hG : HeckeEis.IsEichlerIntegral n f G) :
    ∃ v : ↥(HeckeEis.BinaryForm ℂ n), ∀ τ : UpperHalfPlane, F τ - G τ = v := by sorry
