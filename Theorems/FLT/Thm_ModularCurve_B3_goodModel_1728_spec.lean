import Definitions.FLT.Def_ModularCurve_SpecialisationVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.B3.goodModel_1728_spec :
    IntegralCoeffs (goodModel 1728) ∧ (goodModel 1728).Δ.orderTop = 0 ∧
      ∃ _ : (specialFibre (goodModel 1728)).IsElliptic,
        (specialFibre (goodModel 1728)).j = 1728 := by sorry
