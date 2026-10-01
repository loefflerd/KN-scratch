import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u
theorem WeierstrassCurve.Affine.algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (Polynomial.C Polynomial.X))
      ∉ (placeOfPoint (0 : W.Point)).toValuationSubring := by sorry
