import Definitions.FLT.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
theorem ModularCurve.Period.finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (K : Type) [Field K] :
    Module.finrank K (ModularCurve.Period.parabolicHoms K Γ K)
      + Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
      ≤ Module.finrank K (Additive Γ →+ K) + 1 := by sorry
