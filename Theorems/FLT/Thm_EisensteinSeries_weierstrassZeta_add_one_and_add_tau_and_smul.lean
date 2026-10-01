import Definitions.FLT.Def_EisensteinSeries_WeierstrassZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real MatrixGroups
theorem EisensteinSeries.weierstrassZeta_add_one_and_add_tau_and_smul (τ : UpperHalfPlane) :
    (∀ z : ℂ, (∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) →
        EisensteinSeries.weierstrassZeta τ (z + 1) =
          EisensteinSeries.weierstrassZeta τ z + EisensteinSeries.G2 τ) ∧
    (∀ z : ℂ, (∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) →
        EisensteinSeries.weierstrassZeta τ (z + τ) =
          EisensteinSeries.weierstrassZeta τ z +
            ((τ : ℂ) * EisensteinSeries.G2 τ - 2 * π * Complex.I)) ∧
    (∀ (γ : SL(2, ℤ)) (z : ℂ),
        EisensteinSeries.weierstrassZeta (γ • τ) (z / UpperHalfPlane.denom γ τ) =
          UpperHalfPlane.denom γ τ * EisensteinSeries.weierstrassZeta τ z) := by sorry
