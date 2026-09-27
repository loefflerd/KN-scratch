import Definitions.FLT.Def_ModularCurve_ModularUnit
import Definitions.FLT.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.hasSum_smul_modularUnitSeries_inv_qParam (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => ((((N : ℚ) ^ 12 • (ModularCurve.modularUnitSeries N)⁻¹).coeff m : ℚ) : ℂ) * Function.Periodic.qParam N (τ : ℂ) ^ m) (ModularForm.discriminant (ModularGroup.S • τ) / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • ModularGroup.S • τ)) := by sorry
