import Mathlib
import Definitions.FLT.Def_Isogeny_ConditionalCurrency
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.FLT.Def_WeierstrassCurve_Velu
import Definitions.FLT.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.FLT.Def_WeierstrassCurve_FullKernelQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.exists_functionFieldHom_fullKernelQuotient_pointMapOfPushforward_ker_eq_zmultiples {F : Type*} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    {W : WeierstrassCurve F} [W.toAffine.IsElliptic]
    {Q : W.toAffine.Point} {N : ℕ} [NeZero N] (hord : addOrderOf Q = N)
    (hΔ' : (W.fullKernelQuotient Q N).Δ ≠ 0)
    [(W.fullKernelQuotient Q N).toAffine.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate
      (W.fullKernelQuotient Q N).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred
      (W.fullKernelQuotient Q N).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem
      (W.fullKernelQuotient Q N).toAffine] :
    ∃ (ι : (W.fullKernelQuotient Q N).toAffine.FunctionField
            →ₐ[F] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι),
      ∀ hN : AlgebraicCurve.NormFormulaAlong F ι hfin,
        (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
          = AddSubgroup.zmultiples Q := by sorry
