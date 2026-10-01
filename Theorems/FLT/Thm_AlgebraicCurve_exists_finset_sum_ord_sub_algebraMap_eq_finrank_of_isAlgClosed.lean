import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) (a : k) :
    ∃ S : Finset (Place k F), (∀ P, P ∈ S ↔ 0 < P.ord (x - algebraMap k F a)) ∧
      ∑ P ∈ S, P.ord (x - algebraMap k F a) = (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by sorry
