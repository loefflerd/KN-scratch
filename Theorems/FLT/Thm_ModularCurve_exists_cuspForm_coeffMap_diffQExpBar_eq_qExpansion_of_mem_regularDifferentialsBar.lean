import Mathlib.NumberTheory.ModularForms.QExpansion

import Definitions.FLT.Def_ModularCurve_HeckeDifferential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.exists_cuspForm_coeffMap_diffQExpBar_eq_qExpansion_of_mem_regularDifferentialsBar
    (N : ℕ) [NeZero N] (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    (ω : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])
    (hω : ω ∈ ModularCurve.regularDifferentialsBar N) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      ModularCurve.coeffMap ι₀ (ModularCurve.diffQExpBar N ω) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 f) := by sorry
