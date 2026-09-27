import Mathlib
import Definitions.FLT.Def_ModularCurve_JLinePlaces
import Definitions.FLT.Def_AlgebraicCurve_DivisorPushPull
import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve
theorem ModularCurve.eq_jLinePlaceInfty_iff_ord_jGen_neg (v : AlgebraicCurve.Place ℚ ↥ℚ⟮ModularCurve.jq⟯) :
    v = ModularCurve.jLinePlaceInfty ↔ v.ord ModularCurve.jGen < 0 := by sorry
