import Mathlib.NumberTheory.ModularForms.SlashActions

import Definitions.FLT.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm
theorem HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral
    {n : ℕ} {Γ : Subgroup SL(2, ℤ)} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F)
    (hf : ∀ γ ∈ Γ, (f ∣[((n : ℤ) + 2)] γ) = f) :
    HeckeEis.IsEquivariantPrimitiveWith ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype) F := by sorry
