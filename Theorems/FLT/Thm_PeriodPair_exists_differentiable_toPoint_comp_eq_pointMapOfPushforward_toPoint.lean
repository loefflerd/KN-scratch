import Definitions.FLT.Def_Isogeny_ConditionalCurrency
import Definitions.FLT.Def_PeriodPair_Uniformization
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve
theorem PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint
    (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero)
    [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
    [GenusOnePlaceGate L.weierstrassCurve.toAffine] [GenusOnePlaceGate.IsCentred L.weierstrassCurve.toAffine]
    [AbelTheorem L.weierstrassCurve.toAffine]
    [GenusOnePlaceGate L'.weierstrassCurve.toAffine] [GenusOnePlaceGate.IsCentred L'.weierstrassCurve.toAffine]
    [AbelTheorem L'.weierstrassCurve.toAffine]
    (ι : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ] L.weierstrassCurve.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι) (hN : NormFormulaAlong ℂ ι hfin) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 0 ∈ L'.lattice ∧
      ∀ z : ℂ, L'.toPoint hL' (F z) = pointMapOfPushforward ι hι hfin hN (L.toPoint hL z) := by sorry
