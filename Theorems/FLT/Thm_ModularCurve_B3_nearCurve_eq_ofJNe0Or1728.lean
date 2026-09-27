import Definitions.FLT.Def_ModularCurve_SpecialisationVocab
import Definitions.FLT.Def_ModularCurve_TatePoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve.TatePoint
theorem ModularCurve.B3.nearCurve_eq_ofJNe0Or1728 (j₀ : Qbar) :
    nearCurve j₀ = WeierstrassCurve.ofJNe0Or1728 (jNear j₀) := by sorry
