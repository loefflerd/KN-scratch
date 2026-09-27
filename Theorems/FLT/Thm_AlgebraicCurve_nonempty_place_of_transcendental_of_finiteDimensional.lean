import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
theorem AlgebraicCurve.nonempty_place_of_transcendental_of_finiteDimensional
    (k : Type*) [Field k] {F : Type*} [Field F] [Algebra k F] (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set F)) F)
    [Algebra.IsSeparable ↥(IntermediateField.adjoin k ({x} : Set F)) F] :
    Nonempty (AlgebraicCurve.Place k F) := by sorry
