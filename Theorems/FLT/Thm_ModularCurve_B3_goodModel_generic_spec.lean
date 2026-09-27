import Definitions.FLT.Def_ModularCurve_SpecialisationVocab
import Definitions.FLT.Def_ModularCurve_TatePoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve.TatePoint
theorem ModularCurve.B3.goodModel_generic_spec (j₀ : Qbar) (h0 : j₀ ≠ 0) (h1728 : j₀ ≠ 1728) :
    IntegralCoeffs (goodModel j₀) ∧ (goodModel j₀).Δ.orderTop = 0 ∧
      specialFibre (goodModel j₀) = WeierstrassCurve.ofJ j₀ := by sorry
