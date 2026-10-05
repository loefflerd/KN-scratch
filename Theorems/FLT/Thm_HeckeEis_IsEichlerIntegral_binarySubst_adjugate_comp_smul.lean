import Mathlib.NumberTheory.ModularForms.SlashActions
import Definitions.FLT.Def_HeckeEis_EichlerIntegral

open scoped MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.binarySubst_adjugate_comp_smul {n : ℕ} {f : UpperHalfPlane → ℂ}
    {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hF : HeckeEis.IsEichlerIntegral n f F)
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : 0 < M.det) {β : GL (Fin 2) ℝ}
    (hβM : (β : Matrix (Fin 2) (Fin 2) ℝ) = M.map (algebraMap ℤ ℝ)) :
    HeckeEis.IsEichlerIntegral n (f ∣[((n : ℤ) + 2)] β)
      (fun τ => ((HeckeEis.binarySubst ℂ M.adjugate).toLinearMap.restrict
        (fun _ h => HeckeEis.binarySubst_mem ℂ M.adjugate h)) (F (β • τ))) := by sorry
