import Mathlib.NumberTheory.ModularForms.Discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularCurve.exists_smul_eq_of_E4_cube_div_discriminant_eq (τ τ' : ℍ)
    (h : (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ =
      (ModularForm.E₄ : ℍ → ℂ) τ' ^ 3 / ModularForm.discriminant τ') :
    ∃ γ : SL(2, ℤ), γ • τ = τ' := by sorry
