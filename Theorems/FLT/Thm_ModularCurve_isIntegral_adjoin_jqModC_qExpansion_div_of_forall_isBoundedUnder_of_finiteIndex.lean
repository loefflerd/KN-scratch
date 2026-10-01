import Mathlib.NumberTheory.ModularForms.QExpansion

import Definitions.FLT.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology
theorem ModularCurve.isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder_of_finiteIndex
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (hb : ∀ τ : UpperHalfPlane, Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
      (fun z : UpperHalfPlane => ‖g z / h z‖)) :
    IsIntegral (Algebra.adjoin ℂ ({ModularCurve.jqModC ℂ} : Set (LaurentSeries ℂ)))
      (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) /
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑h)) := by sorry
