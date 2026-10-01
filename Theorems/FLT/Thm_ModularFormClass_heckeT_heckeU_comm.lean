import Mathlib.NumberTheory.ModularForms.Basic

import Definitions.FLT.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularFormClass.heckeT_heckeU_comm {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p q : ℕ} (hpq : Nat.Coprime p q) : ModularForm.heckeT k p (ModularForm.heckeU k q ⇑f) = ModularForm.heckeU k q (ModularForm.heckeT k p ⇑f) := by sorry
