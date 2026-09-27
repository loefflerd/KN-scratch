import Definitions.FLT.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.transcendental_jqModC (K : Type*) [CommRing K] :
    Transcendental K (jqModC K) := by sorry
