import Definitions.FLT.Def_ModularCurve_SpecialisationVocab
import Definitions.FLT.Def_ModularCurve_TatePoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve.TatePoint
theorem ModularCurve.B3.isElliptic_specialFibre_goodModel (j₀ : Qbar) :
    (specialFibre (goodModel j₀)).IsElliptic := by sorry
