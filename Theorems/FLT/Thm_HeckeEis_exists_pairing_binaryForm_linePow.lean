import Definitions.FLT.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem HeckeEis.exists_pairing_binaryForm_linePow (n : ℕ) :
    ∃ B : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ℂ,
      (∀ (g : SL(2, ℤ)) (P Q : ↥(HeckeEis.BinaryForm ℂ n)),
          B (HeckeEis.binaryFormRepSL ℂ n g P) (HeckeEis.binaryFormRepSL ℂ n g Q) = B P Q) ∧
      (∀ P Q : ↥(HeckeEis.BinaryForm ℂ n), B Q P = (-1) ^ n * B P Q) ∧
      (∀ P : ↥(HeckeEis.BinaryForm ℂ n), (∀ Q : ↥(HeckeEis.BinaryForm ℂ n), B P Q = 0) → P = 0) ∧
      (∀ τ σ : ℂ, B (HeckeEis.linePow n τ) (HeckeEis.linePow n σ) = (τ - σ) ^ n) := by sorry
