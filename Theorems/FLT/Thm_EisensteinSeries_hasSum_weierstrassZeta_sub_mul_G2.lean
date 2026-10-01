import Definitions.FLT.Def_EisensteinSeries_WeierstrassZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real
theorem EisensteinSeries.hasSum_weierstrassZeta_sub_mul_G2 (τ : UpperHalfPlane) (z : ℂ)
    (hz : ∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) :
    HasSum (fun m : ℕ => π * Complex.cot (π * (z + ((m : ℂ) + 1) * τ)) +
        π * Complex.cot (π * (z - ((m : ℂ) + 1) * τ)))
      (EisensteinSeries.weierstrassZeta τ z - z * EisensteinSeries.G2 τ -
        π * Complex.cot (π * z)) := by sorry
