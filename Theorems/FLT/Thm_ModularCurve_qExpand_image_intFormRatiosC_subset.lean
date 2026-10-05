import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups in
theorem ModularCurve.qExpand_image_intFormRatiosC_subset (K : Type*) [Field K]
    {Γ Γ' : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (ℓ : ℕ) [NeZero ℓ]
    (hΓ' : ∀ γ ∈ Γ', ∃ γ₁ ∈ Γ,
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1) :
    ModularCurve.qExpand K ℓ '' ModularCurve.intFormRatiosC K Γ ⊆
      ModularCurve.intFormRatiosC K Γ' := by sorry
