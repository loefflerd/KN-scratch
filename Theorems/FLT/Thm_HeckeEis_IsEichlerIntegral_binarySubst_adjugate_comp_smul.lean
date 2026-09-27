import Mathlib
import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm
theorem HeckeEis.IsEichlerIntegral.binarySubst_adjugate_comp_smul {n : ℕ} {f : UpperHalfPlane → ℂ}
    {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hF : HeckeEis.IsEichlerIntegral n f F)
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : 0 < M.det) {β : GL (Fin 2) ℝ}
    (hβM : (β : Matrix (Fin 2) (Fin 2) ℝ) = M.map (algebraMap ℤ ℝ)) :
    HeckeEis.IsEichlerIntegral n (f ∣[((n : ℤ) + 2)] β)
      (fun τ => ((HeckeEis.binarySubst ℂ M.adjugate).toLinearMap.restrict
        (fun _ h => HeckeEis.binarySubst_mem ℂ M.adjugate h)) (F (β • τ))) := by sorry
