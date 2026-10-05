module

public import Definitions.FLT.Def_WeierstrassCurve_VeluOrderTwo

import Theorems.FLT.Thm_WeierstrassCurve_Delta_eq_veluGx_sq_mul_velu2QuadDisc
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_velu2QuadDisc_ne_zero_of_two_torsion

open WeierstrassCurve WeierstrassCurve.Affine in
theorem solution {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ : R} (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    W.velu2QuadDisc x₀ ≠ 0 := by
  intro h
  exact hΔ (by rw [Delta_eq_veluGx_sq_mul_velu2QuadDisc hQ hgy, h]; ring)

end S_WeierstrassCurve_velu2QuadDisc_ne_zero_of_two_torsion
end P2MW
export P2MW.S_WeierstrassCurve_velu2QuadDisc_ne_zero_of_two_torsion (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R}
theorem velu2QuadDisc_ne_zero_of_two_torsion {x₀ y₀ : R} (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    W.velu2QuadDisc x₀ ≠ 0 := _root_.P2MW.S_WeierstrassCurve_velu2QuadDisc_ne_zero_of_two_torsion.solution hΔ hQ hgy
end WeierstrassCurve

end publicSection
