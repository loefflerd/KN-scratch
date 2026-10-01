import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u
theorem WeierstrassCurve.Affine.GenusOnePlaceGate.ext_of_isCentred
    {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    [IsDedekindDomain W.CoordinateRing]
    (g₁ g₂ : WeierstrassCurve.Affine.GenusOnePlaceGate W)
    (h₁ : @WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred F _ W g₁)
    (h₂ : @WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred F _ W g₂) :
    g₁ = g₂ := by sorry
