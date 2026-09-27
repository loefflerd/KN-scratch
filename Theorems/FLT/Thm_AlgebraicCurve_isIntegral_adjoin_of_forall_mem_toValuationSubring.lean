import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.isIntegral_adjoin_of_forall_mem_toValuationSubring
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (t z : F)
    (h : ∀ v : AlgebraicCurve.Place K F, t ∈ v.toValuationSubring → z ∈ v.toValuationSubring) :
    IsIntegral (Algebra.adjoin K ({t} : Set F)) z := by sorry
