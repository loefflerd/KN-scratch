import Definitions.FLT.Def_ModularCurve_SpecialisationVocab
import Definitions.FLT.Def_ModularCurve_TatePoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve.TatePoint
open scoped Classical
theorem ModularCurve.B3.isElliptic_specialFibre (W : WeierstrassCurve H)
    (hW : IntegralCoeffs W) (hΔ : W.Δ.orderTop = 0) : (specialFibre W).IsElliptic := by sorry
