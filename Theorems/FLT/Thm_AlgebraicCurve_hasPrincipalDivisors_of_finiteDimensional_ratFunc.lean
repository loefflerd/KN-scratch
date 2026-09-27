import Definitions.FLT.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.FieldTheory.RatFunc.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc (K : Type*) [Field K] [CharZero K] (F' : Type*)
    [Field F'] [Algebra K F'] [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F'] :
    HasPrincipalDivisors K F' := by sorry
