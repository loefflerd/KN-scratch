import Mathlib
import Definitions.FLT.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf (Γ : Subgroup SL(2, ℤ))
    (f : CuspForm Γ 2) {F : UpperHalfPlane → ℂ}
    (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F) (γ : Γ) :
    ModularCurve.periodOf Γ γ f =
      F ((γ : SL(2, ℤ)) • UpperHalfPlane.I) - F UpperHalfPlane.I := by sorry
