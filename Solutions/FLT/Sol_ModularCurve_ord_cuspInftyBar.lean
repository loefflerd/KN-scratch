import Definitions.FLT.Def_ModularCurve_AtkinLehner
import Theorems.FLT.Thm_ModularCurve_ord_qInftyPlaceBar
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_cuspInftyBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (f : modularFunctionFieldBar N) :
    (cuspInftyBar N).ord f = (f : LaurentSeries (AlgebraicClosure ℚ)).order :=
  ModularCurve.ord_qInftyPlaceBar (AlgebraicClosure ℚ) _ f

end S_ModularCurve_ord_cuspInftyBar
end P2MW
export P2MW.S_ModularCurve_ord_cuspInftyBar (solution)
