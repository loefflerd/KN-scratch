import Definitions.FLT.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.isCusp_iff_ord_neg {K : Type*} {E : Type*} [Field K] [Field E] [Algebra K E] (j : E) (v : Place K E) : IsCusp j v ↔ v.ord j < 0 := by sorry
