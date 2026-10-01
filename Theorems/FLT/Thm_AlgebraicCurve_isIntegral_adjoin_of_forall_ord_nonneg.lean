import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (t : F) [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] [AlgebraicCurve.HasPrincipalDivisors K F] (z : F) (hz : ∀ v : AlgebraicCurve.Place K F, 0 ≤ v.ord t → 0 ≤ v.ord z) : IsIntegral (Algebra.adjoin K ({t} : Set F)) z := by sorry
