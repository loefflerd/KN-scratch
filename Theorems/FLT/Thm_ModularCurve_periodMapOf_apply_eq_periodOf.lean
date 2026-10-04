import Mathlib
import Definitions.FLT.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem ModularCurve.periodMapOf_apply_eq_periodOf (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : CuspForm Γ 2) (γ : Γ) :
    ModularCurve.periodMapOf Γ f (Additive.ofMul γ) = ModularCurve.periodOf Γ γ f := by sorry
