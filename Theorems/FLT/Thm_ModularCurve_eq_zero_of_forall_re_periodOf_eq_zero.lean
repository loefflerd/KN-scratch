import Mathlib
import Definitions.FLT.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : CuspForm Γ 2)
    (h : ∀ γ : Γ, (ModularCurve.periodOf Γ γ f).re = 0) : f = 0 := by sorry
