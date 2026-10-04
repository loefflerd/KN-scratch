import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.six_mul_degree_eq_mul_finrank_of_forall_eq_weightFloor_of_ord_eq_three_two
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (y : F) (hy : Transcendental k y)
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin k ({y} : Set F)) F)
    (h0 : ∀ w : AlgebraicCurve.Place k F, 0 < w.ord y → w.ord y = 3)
    (h1728 : ∀ w : AlgebraicCurve.Place k F, 0 < w.ord (y - 1728) → w.ord (y - 1728) = 2)
    (m : ℕ) (D : AlgebraicCurve.Divisor k F)
    (hD : ∀ w : AlgebraicCurve.Place k F,
      D w = (if 0 < w.ord y then (2 * (m : ℤ) * w.ord y) / 3 else 0)
          + (if 0 < w.ord (y - 1728) then ((m : ℤ) * w.ord (y - 1728)) / 2 else 0)
          + (if w.ord y < 0 then (m : ℤ) * w.ord y else 0)) :
    6 * D.degree = (m : ℤ) * (Module.finrank ↥(IntermediateField.adjoin k ({y} : Set F)) F : ℤ) := by sorry
