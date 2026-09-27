import Definitions.KN.Def_MonoidAlgebra_Augmentation
import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Theorems.FLT.Thm_MonoidAlgebra_isLocalRing_of_isPGroup

set_option autoImplicit false
noncomputable section

/-- In the group ring of a finite `p`-group over a commutative local ring of
residue characteristic `p`, an element is a unit exactly when its augmentation
is a unit. This is the augmentation corollary of
`MonoidAlgebra.isLocalRing_of_isPGroup`. -/
theorem MonoidAlgebra.isUnit_iff_augmentation_of_isPGroup_v2
    {R G : Type*} [CommRing R] [IsLocalRing R]
    {p : ℕ} [Fact p.Prime] [CommGroup G] [Finite G]
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hG : IsPGroup p G) (x : MonoidAlgebra R G) :
    IsUnit x ↔ IsUnit (MonoidAlgebra.augmentation R G x) := by sorry
