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
theorem solution
    {R G : Type*} [CommRing R] [IsLocalRing R]
    {p : ℕ} [Fact p.Prime] [CommGroup G] [Finite G]
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hG : IsPGroup p G) (x : MonoidAlgebra R G) :
    IsUnit x ↔ IsUnit (MonoidAlgebra.augmentation R G x) := by
  have := MonoidAlgebra.isLocalRing_of_isPGroup hp hG
  let aug := MonoidAlgebra.augmentation R G
  have hsurj : Function.Surjective aug := by
    intro r
    refine ⟨MonoidAlgebra.single 1 r, ?_⟩
    simp [aug, MonoidAlgebra.augmentation]
  have : IsLocalHom aug := IsLocalHom.of_surjective aug hsurj
  exact (isUnit_map_iff aug x).symm
