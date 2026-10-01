import Definitions.FLT.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups in
theorem CohCarrier.index_gammaH_eq_index_gamma0_mul_index (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).index = (CongruenceSubgroup.Gamma0 M).index * H.index := by sorry
