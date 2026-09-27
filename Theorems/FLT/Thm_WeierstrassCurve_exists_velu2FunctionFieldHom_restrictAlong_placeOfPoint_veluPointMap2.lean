import Mathlib
import Definitions.FLT.Def_Isogeny_ConditionalCurrency
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.FLT.Def_WeierstrassCurve_VeluPointMap2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
theorem WeierstrassCurve.exists_velu2FunctionFieldHom_restrictAlong_placeOfPoint_veluPointMap2
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    {W : WeierstrassCurve F} [W.IsElliptic]
    {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ' : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)
    [(W.veluQuotient2 x₀ y₀).IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate (W.veluQuotient2 x₀ y₀).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W.veluQuotient2 x₀ y₀).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (W.veluQuotient2 x₀ y₀).toAffine] :
    ∃ (ι : (W.veluQuotient2 x₀ y₀).toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι),
      ∀ P : W.toAffine.Point,
        (WeierstrassCurve.Affine.placeOfPoint P).restrictAlong ι hι
          = WeierstrassCurve.Affine.placeOfPoint
              (WeierstrassCurve.veluPointMap2 two_ne_zero hQ hgy hΔ' P) := by sorry
