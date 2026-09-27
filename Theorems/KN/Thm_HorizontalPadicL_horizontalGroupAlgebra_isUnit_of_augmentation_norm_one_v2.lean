import Definitions.KN.Def_KN_SeededThetaConstructionV2B

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- The standard unit criterion for a group algebra of a finite `p`-group over
the valuation ring of `ℂ_p`: an element is a unit if its augmentation is a unit.
For the explicit horizontal group, being a unit in the coefficient ring is
equivalent to the displayed norm-one condition. -/
theorem horizontalGroupAlgebra_isUnit_of_augmentation_norm_one_v2
    {p : ℕ} [Fact p.Prime] (m : ℕ → ℕ) (A : Finset ℕ)
    (x : HorizontalGroupAlgebra (𝓞_ℂ_[p]).toSubring p m A)
    (haug :
      ‖((horizontalAugmentation x : (𝓞_ℂ_[p]).toSubring) : ℂ_[p])‖ = 1) :
    IsUnit x := by sorry

end HorizontalPadicL
