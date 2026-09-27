import Definitions.FLT.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularForm.exists_degeneracy_Gamma0 {k : ℤ} {M N d : ℕ} [NeZero N] (hd : d * M ∣ N) (f : ModularForm (CongruenceSubgroup.Gamma0 M) k) : ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ) := by sorry
