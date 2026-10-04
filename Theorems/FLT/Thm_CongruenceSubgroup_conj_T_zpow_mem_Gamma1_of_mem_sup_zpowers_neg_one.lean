import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem CongruenceSubgroup.conj_T_zpow_mem_Gamma1_of_mem_sup_zpowers_neg_one (M : ℕ) (hM : ¬ M ∣ 4)
    (σ : SL(2, ℤ)) (h : ℤ) (hmem : σ * ModularGroup.T ^ h * σ⁻¹ ∈ CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) :
    σ * ModularGroup.T ^ h * σ⁻¹ ∈ CongruenceSubgroup.Gamma1 M := by sorry
