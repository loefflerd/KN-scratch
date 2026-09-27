import Mathlib
import Definitions.FLT.Def_ModularCurve_X1
import Definitions.FLT.Def_ModularCurve_JqCoeff
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
theorem ModularCurve.exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex]
    (τ : AlgebraicClosure ℚ →ₐ[ℚ] K)
    (Ψ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) →+*
           ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hΨ : ∀ f, ((Ψ f : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ))) : LaurentSeries K)
             = ModularCurve.coeffMap τ.toRingHom (f : LaurentSeries (AlgebraicClosure ℚ)))
    (P : AlgebraicCurve.Place K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hP : ∃ f, P.ord (Ψ f) ≠ 0) :
    ∃ P₀ : AlgebraicCurve.Place (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)),
      ∀ f, P.ord (Ψ f) = P₀.ord f := by sorry
