import Mathlib
import Definitions.FLT.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem HeckeEis.le_finrank_fixed_S_and_ST_binaryFormRepSL (n : ℕ) (hn : Even n) :
    n + 1 - 2 * ((n + 2) / 4) ≤ Module.finrank ℂ ↥(LinearMap.ker (HeckeEis.binaryFormRepSL ℂ n ModularGroup.S - 1)) ∧
    n + 1 - 2 * ((n + 2) / 3)
      ≤ Module.finrank ℂ ↥(LinearMap.ker (HeckeEis.binaryFormRepSL ℂ n (ModularGroup.S * ModularGroup.T) - 1)) := by sorry
