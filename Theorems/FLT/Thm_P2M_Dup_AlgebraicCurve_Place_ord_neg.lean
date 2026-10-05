module

public import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.FLT.Def_AlgebraicCurve_PlacesOverDVR

import Theorems.FLT.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_neg

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_algebraMap"
namespace FF2S
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_neg (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [neg_eq_neg_one_mul, v.ord_mul (neg_ne_zero.mpr one_ne_zero) hf,
      show (-1 : F) = algebraMap K F (-1) by simp, v.ord_algebraMap, zero_add]

end AlgebraicCurve.FF2S

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) (f : F) :
    v.ord (-f) = v.ord f :=
  AlgebraicCurve.FF2S.ord_neg v f

end S_AlgebraicCurve_Place_ord_neg
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_neg (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem P2M.Dup.AlgebraicCurve.Place.ord_neg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) (f : F) :
    v.ord (-f) = v.ord f := _root_.P2MW.S_AlgebraicCurve_Place_ord_neg.solution v f

end publicSection
