import Definitions.FLT.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem HeckeEis.binaryFormRepSL_neg_one_apply (K : Type*) [CommRing K] (n : ℕ) (P : ↥(HeckeEis.BinaryForm K n)) :
    HeckeEis.binaryFormRepSL K n (-1) P = ((-1 : K) ^ n) • P := by sorry
