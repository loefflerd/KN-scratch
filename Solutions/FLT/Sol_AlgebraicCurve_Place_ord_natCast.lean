import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.FLT.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_natCast

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_algebraMap"
namespace FF2S
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_natCast (v : Place K F) (n : ℕ) : v.ord (n : F) = 0 := by
  rw [show (n : F) = algebraMap K F n by simp]
  exact v.ord_algebraMap n

end AlgebraicCurve.FF2S

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) (n : ℕ) :
    v.ord (n : F) = 0 :=
  AlgebraicCurve.FF2S.ord_natCast v n

end S_AlgebraicCurve_Place_ord_natCast
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_natCast (solution)
