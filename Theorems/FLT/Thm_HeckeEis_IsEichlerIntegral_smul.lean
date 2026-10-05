import Definitions.FLT.Def_HeckeEis_EichlerIntegral

open scoped MatrixGroups
theorem HeckeEis.IsEichlerIntegral.smul {n : ℕ} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (c : ℂ) :
    HeckeEis.IsEichlerIntegral n (c • f) (c • F) := by sorry
