import Mathlib
import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm
theorem HeckeEis.IsEichlerIntegral.slash {n : ℕ} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (δ : SL(2, ℤ)) :
    HeckeEis.IsEichlerIntegral n (f ∣[((n : ℤ) + 2)] δ) (fun τ => HeckeEis.binaryFormRepSL ℂ n δ⁻¹ (F (δ • τ))) := by sorry
