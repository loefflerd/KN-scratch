import Definitions.FLT.Def_ModularCurve_X0
import Theorems.FLT.Thm_ModularCurve_le_dedekindPsi
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_dedekindPsi_pos

open ModularCurve

theorem solution (N : ℕ) (hN : N ≠ 0) : 0 < dedekindPsi N :=
  lt_of_lt_of_le (Nat.pos_of_ne_zero hN) (ModularCurve.le_dedekindPsi N hN)

end S_ModularCurve_dedekindPsi_pos
end P2MW
export P2MW.S_ModularCurve_dedekindPsi_pos (solution)
