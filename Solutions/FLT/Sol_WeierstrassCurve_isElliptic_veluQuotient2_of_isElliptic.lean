import Mathlib
import Definitions.FLT.Def_WeierstrassCurve_VeluOrderTwo
import Theorems.FLT.Thm_WeierstrassCurve_veluQuotient2_Delta_ne_zero
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic

open WeierstrassCurve WeierstrassCurve.Affine in
theorem solution {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic] {x₀ y₀ : F}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    (W.veluQuotient2 x₀ y₀).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (veluQuotient2_Delta_ne_zero W.isUnit_Δ.ne_zero hQ hgy)⟩

end S_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
end P2MW
export P2MW.S_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic (solution)
