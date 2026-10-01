import Definitions.FLT.Def_EisensteinSeries_WeierstrassZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real MatrixGroups Matrix
theorem EisensteinSeries.eisensteinG1_apply_smul_and_eisensteinG1_add (N : ℕ) [NeZero N]
    (τ : UpperHalfPlane) :
    (∀ (γ : SL(2, ℤ)) (v : Fin 2 → ℤ),
        EisensteinSeries.eisensteinG1 N v (γ • τ) =
          UpperHalfPlane.denom γ τ *
            EisensteinSeries.eisensteinG1 N (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ) ∧
    (∀ v w : Fin 2 → ℤ, (¬ ∀ i, (N : ℤ) ∣ v i) →
        EisensteinSeries.eisensteinG1 N (v + (N : ℤ) • w) τ =
          EisensteinSeries.eisensteinG1 N v τ) := by sorry
