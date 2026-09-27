import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    ∃ S : Finset (Place k F), (∀ P, P ∈ S ↔ P.ord x < 0) ∧
      ∑ P ∈ S, (-P.ord x) = (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by sorry
