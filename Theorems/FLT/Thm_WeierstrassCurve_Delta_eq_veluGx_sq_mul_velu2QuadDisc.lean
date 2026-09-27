import Mathlib
import Definitions.FLT.Def_WeierstrassCurve_VeluOrderTwo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R}
open Affine
theorem Delta_eq_veluGx_sq_mul_velu2QuadDisc {x₀ y₀ : R}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    W.Δ = W.veluGx x₀ y₀ ^ 2 * W.velu2QuadDisc x₀ := by sorry
