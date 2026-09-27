import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.Place.exists_forall_ord_eq_finset {K F : Type*} [Field K] [Field F] [Algebra K F] (S : Finset (AlgebraicCurve.Place K F)) (n : AlgebraicCurve.Place K F → ℤ) :
    ∃ g : F, g ≠ 0 ∧ ∀ v ∈ S, v.ord g = n v := by sorry
