import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (j : F) (hj : Transcendental K j) [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F] {x : F} (hx : ∀ v : Place K F, v.ord x = 0) : x ∈ (algebraMap K F).range := by sorry
