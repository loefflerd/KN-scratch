import Mathlib
import Definitions.FLT.Def_ModularCurve_JLinePlaces
import Definitions.FLT.Def_AlgebraicCurve_DivisorPushPull
import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve
theorem ModularCurve.eq_jLinePlaceZero_iff_ord_jGen_pos (v : AlgebraicCurve.Place ℚ ↥ℚ⟮ModularCurve.jq⟯) :
    v = ModularCurve.jLinePlaceZero ↔ 0 < v.ord ModularCurve.jGen := by sorry
