import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Theorems.FLT.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_finiteDimensional_Gamma0

open UpperHalfPlane ModularForm SlashInvariantForm Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Topology Manifold Pointwise

noncomputable section

theorem solution (N : ℕ) [NeZero N] (k : ℤ) : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) := by
  exact CuspForm.finiteDimensional_of_isArithmetic _ k
end

end S_CuspForm_finiteDimensional_Gamma0
end P2MW
export P2MW.S_CuspForm_finiteDimensional_Gamma0 (solution)
