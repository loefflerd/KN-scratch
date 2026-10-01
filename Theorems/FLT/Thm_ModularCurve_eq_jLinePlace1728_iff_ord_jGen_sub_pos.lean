import Definitions.FLT.Def_ModularCurve_JLinePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve
theorem ModularCurve.eq_jLinePlace1728_iff_ord_jGen_sub_pos (v : AlgebraicCurve.Place ℚ ↥ℚ⟮ModularCurve.jq⟯) :
    v = ModularCurve.jLinePlace1728 ↔ 0 < v.ord (ModularCurve.jGen - 1728) := by sorry
