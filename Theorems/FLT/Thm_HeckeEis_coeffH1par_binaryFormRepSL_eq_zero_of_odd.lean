import Mathlib
import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem HeckeEis.coeffH1par_binaryFormRepSL_eq_zero_of_odd (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) (N n : ℕ) (hn : Odd n)
    (x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype)) : x = 0 := by sorry
