import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem CongruenceSubgroup.eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq (M : ℕ) (hM : 4 ≤ M)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 M ∨ -γ ∈ CongruenceSubgroup.Gamma1 M)
    (τ : UpperHalfPlane) (hτ : γ • τ = τ) : γ = 1 ∨ γ = -1 := by sorry
