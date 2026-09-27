import Definitions.FLT.Def_ModularCurve_PeriodMap
import Mathlib.LinearAlgebra.Basis.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ)),
      ∀ (R : Type*) [CommRing R] [IsAddTorsionFree R],
        ∃ bR : Module.Basis (Fin n) R (ModularCurve.Period.parabolicHoms R Γ R),
          ∀ i, (bR i : Additive Γ →+ R) = (Int.castAddHom R).comp (b i : Additive Γ →+ ℤ) := by sorry
