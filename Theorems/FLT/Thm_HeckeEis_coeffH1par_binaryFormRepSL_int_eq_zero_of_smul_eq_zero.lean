import Mathlib
import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Definitions.FLT.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem HeckeEis.coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero (n N : ℕ) [NeZero N] (m : ℤ) (hm : m ≠ 0)
    (x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hx : m • x = 0) : x = 0 := by sorry
