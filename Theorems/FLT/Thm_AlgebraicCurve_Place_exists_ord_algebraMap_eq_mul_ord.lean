import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.Place.exists_ord_algebraMap_eq_mul_ord {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] (w : Place K F') (v : Place K F) (hv : v.toValuationSubring = w.toValuationSubring.comap (algebraMap F F')) : ∃ e : ℕ, 0 < e ∧ ∀ f : F, w.ord (algebraMap F F' f) = e * v.ord f := by sorry
