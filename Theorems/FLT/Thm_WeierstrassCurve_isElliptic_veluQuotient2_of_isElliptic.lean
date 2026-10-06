module

public import Definitions.FLT.Def_WeierstrassCurve_VeluOrderTwo

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Theorems.FLT.Thm_WeierstrassCurve_veluQuotient2_Delta_ne_zero
import Definitions.FLT.Def_P2M_Util

section privateSection

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

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve
variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic] {x₀ y₀ : F}
theorem isElliptic_veluQuotient2_of_isElliptic
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    (W.veluQuotient2 x₀ y₀).IsElliptic := _root_.P2MW.S_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic.solution hQ hgy
end WeierstrassCurve

end publicSection
