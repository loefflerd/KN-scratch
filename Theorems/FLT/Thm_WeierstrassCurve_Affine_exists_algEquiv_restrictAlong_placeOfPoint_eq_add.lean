import Definitions.FLT.Def_AlgebraicCurve_Correspondence
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u
theorem WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (R : W.Point) :
    ∃ (τ : W.FunctionField ≃ₐ[F] W.FunctionField) (hτ : τ.toAlgHom.toRingHom.IsIntegral),
      ∀ Q : W.Point, (placeOfPoint Q).restrictAlong τ.toAlgHom hτ = placeOfPoint (Q + R) := by sorry
