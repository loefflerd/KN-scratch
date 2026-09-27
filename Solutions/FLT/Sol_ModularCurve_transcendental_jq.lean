import Definitions.FLT.Def_ModularCurve_X0
import Theorems.FLT.Thm_ModularCurve_aeval_jq_eq_zero
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_transcendental_jq

open ModularCurve IntermediateField

noncomputable section

theorem solution : Transcendental ℚ jq :=
  transcendental_iff.mpr fun _ hp => ModularCurve.aeval_jq_eq_zero hp

end

end S_ModularCurve_transcendental_jq
end P2MW
export P2MW.S_ModularCurve_transcendental_jq (solution)
