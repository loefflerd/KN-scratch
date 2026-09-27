import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.E4_cube_div_discriminant_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) : ModularForm.E₄ (γ • τ) ^ 3 / ModularForm.discriminant (γ • τ) = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := by sorry
