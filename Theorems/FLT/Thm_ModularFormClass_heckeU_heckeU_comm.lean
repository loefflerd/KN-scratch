import Mathlib.NumberTheory.ModularForms.Basic

import Definitions.FLT.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularFormClass.heckeU_heckeU_comm {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (p q : ℕ) : ModularForm.heckeU k p (ModularForm.heckeU k q ⇑f) = ModularForm.heckeU k q (ModularForm.heckeU k p ⇑f) := by sorry
