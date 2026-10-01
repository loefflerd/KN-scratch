import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable (K F : Type*) [Field K] [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    IsCurveOver K F := by sorry
