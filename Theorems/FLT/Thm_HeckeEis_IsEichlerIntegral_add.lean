import Definitions.FLT.Def_HeckeEis_EichlerIntegral

open scoped MatrixGroups
theorem HeckeEis.IsEichlerIntegral.add {n : ℕ} {f g : UpperHalfPlane → ℂ} {F G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (hG : HeckeEis.IsEichlerIntegral n g G) :
    HeckeEis.IsEichlerIntegral n (f + g) (F + G) := by sorry
