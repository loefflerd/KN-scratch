import Definitions.FLT.Def_Isogeny_ConditionalCurrency
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.FLT.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.FLT.Def_WeierstrassCurve_Velu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples_of_oddOrder
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    {W : WeierstrassCurve F} [W.toAffine.IsElliptic]
    {Q : W.toAffine.Point} {n : ℕ} (hord : addOrderOf Q = 2 * n + 1)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    [(W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine] :
    ∃ (ι : (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField
            →ₐ[F] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι),
      ∀ hN : AlgebraicCurve.NormFormulaAlong F ι hfin,
        (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
          = AddSubgroup.zmultiples Q := by sorry
