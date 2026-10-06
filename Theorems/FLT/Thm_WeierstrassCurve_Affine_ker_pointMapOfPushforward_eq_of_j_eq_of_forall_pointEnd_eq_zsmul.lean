import Definitions.FLT.Def_Isogeny_ConditionalCurrency
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u
theorem WeierstrassCurve.Affine.ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    (hNs : ∀ D : WeierstrassCurve.Affine.IsogenyEndDatum W.toAffine,
      AlgebraicCurve.NormFormulaAlong F D.ι D.hfin)
    (hEnd : ∀ D : WeierstrassCurve.Affine.IsogenyEndDatum W.toAffine,
      ∃ m : ℤ, ∀ P : W.toAffine.Point, D.pointEnd (hNs D) P = m • P)
    (V V' : WeierstrassCurve F) [V.IsElliptic] [V'.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate V.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem V.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate V'.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem V'.toAffine]
    (ι : V.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι)
    (hN : AlgebraicCurve.NormFormulaAlong F ι hfin)
    (ι' : V'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (hι' : ι'.toRingHom.IsIntegral) (hfin' : AlgebraicCurve.FiniteAlong F ι')
    (hN' : AlgebraicCurve.NormFormulaAlong F ι' hfin')
    (hcard : Nat.card (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
      = Nat.card (WeierstrassCurve.Affine.pointMapOfPushforward ι' hι' hfin' hN').ker)
    (hj : V.j = V'.j) :
    (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
      = (WeierstrassCurve.Affine.pointMapOfPushforward ι' hι' hfin' hN').ker := by sorry
