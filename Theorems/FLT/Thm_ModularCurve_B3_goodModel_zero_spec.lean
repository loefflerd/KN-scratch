import Definitions.FLT.Def_ModularCurve_SpecialisationVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.B3.goodModel_zero_spec :
    IntegralCoeffs (goodModel 0) ∧ (goodModel 0).Δ.orderTop = 0 ∧
      ∃ _ : (specialFibre (goodModel 0)).IsElliptic, (specialFibre (goodModel 0)).j = 0 := by sorry
