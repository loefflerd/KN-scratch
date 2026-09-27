import Definitions.FLT.Def_ModularCurve_SpecialisationVocab
import Definitions.FLT.Def_ModularCurve_TatePoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve
open ModularCurve.TatePoint
theorem ModularCurve.B3.exists_variableChange_specialFibre_goodModel (j₀ : Qbar) :
    ∃ C : VariableChange Qbar,
      C • specialFibre (goodModel j₀) = WeierstrassCurve.ofJ j₀ := by sorry
