import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_ModularCurve_LaurentCoeff
import Definitions.FLT.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.adjoin_jBar_jNBar_eq_top (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] :
    IntermediateField.adjoin L
      ({⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩,
        ⟨coeffEmb L (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange L (jqd_mem_full N (dvd_refl N))⟩} :
        Set (laurentBaseChange L (modularFunctionFieldFull N)))
      = ⊤ := by sorry
