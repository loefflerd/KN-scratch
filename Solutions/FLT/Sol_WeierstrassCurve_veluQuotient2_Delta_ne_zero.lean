import Mathlib
import Definitions.FLT.Def_WeierstrassCurve_VeluOrderTwo
import Theorems.FLT.Thm_WeierstrassCurve_veluQuotient2_Delta_eq
import Theorems.FLT.Thm_WeierstrassCurve_veluGx_ne_zero_of_two_torsion
import Theorems.FLT.Thm_WeierstrassCurve_velu2QuadDisc_ne_zero_of_two_torsion
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_veluQuotient2_Delta_ne_zero

open WeierstrassCurve WeierstrassCurve.Affine in
theorem solution {R : Type*} [CommRing R] [NoZeroDivisors R] {W : WeierstrassCurve R}
    {x₀ y₀ : R} (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    (W.veluQuotient2 x₀ y₀).Δ ≠ 0 := by
  rw [veluQuotient2_Delta_eq hQ hgy]
  exact mul_ne_zero (veluGx_ne_zero_of_two_torsion hΔ hQ hgy)
    (pow_ne_zero 2 (velu2QuadDisc_ne_zero_of_two_torsion hΔ hQ hgy))

end S_WeierstrassCurve_veluQuotient2_Delta_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_veluQuotient2_Delta_ne_zero (solution)
