import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups
theorem CuspForm.finiteDimensional_Gamma0 (N : ℕ) [NeZero N] (k : ℤ) : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) := by sorry
