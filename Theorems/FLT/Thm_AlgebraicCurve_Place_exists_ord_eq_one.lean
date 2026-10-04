module

public import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_ord_eq_one

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) :
    ∃ t : F, v.ord t = 1 :=
  let ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  ⟨π, v.ord_coe_irreducible hπ⟩

end S_AlgebraicCurve_Place_exists_ord_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_ord_eq_one (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.Place.exists_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) :
    ∃ t : F, v.ord t = 1 := _root_.P2MW.S_AlgebraicCurve_Place_exists_ord_eq_one.solution v

end publicSection
