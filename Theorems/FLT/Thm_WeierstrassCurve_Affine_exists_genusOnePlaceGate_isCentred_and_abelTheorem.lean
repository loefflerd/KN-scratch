import Mathlib
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePic0
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

universe u
theorem WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [IsDedekindDomain W.CoordinateRing] [AlgebraicCurve.HasPrincipalDivisors F W.FunctionField] :
    ∃ g : WeierstrassCurve.Affine.GenusOnePlaceGate W,
      @WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred F _ W g
        ∧ @WeierstrassCurve.Affine.AbelTheorem F _ _ W g := by sorry
