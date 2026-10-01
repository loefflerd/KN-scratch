import Definitions.FLT.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem PeriodPair.isUniformization_toPoint (L : PeriodPair) (h : L.DiscriminantNeZero) :
    L.IsUniformization h := by sorry
