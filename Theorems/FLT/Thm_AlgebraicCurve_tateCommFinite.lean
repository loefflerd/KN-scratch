import Definitions.FLT.Def_AlgebraicCurve_TateResidueCurrency

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.tateCommFinite
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [∀ u : AlgebraicCurve.Place K L, u.FiniteResidue] :
    ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K L := by sorry
