import Definitions.FLT.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F) {w : Place K F'}
    (hw : w.restrict F = v) :
    w.ramificationIndex F = (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' (Place.fiberCenter F' v hw).asIdeal := by sorry
