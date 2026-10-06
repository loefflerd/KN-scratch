import Definitions.FLT.Def_AlgebraicCurve_TateResidueCurrency

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.tateTraceCompat_of_isSeparable
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F] [Algebra.IsSeparable E F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K E]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue] [∀ v : AlgebraicCurve.Place K E, v.FiniteResidue]
    (hfinF : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K F)
    (hfinE : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K E) :
    ModularCurve.KwF4gRRTate.KwF4gRRTateTraceCompat K F E hfinF hfinE := by sorry
