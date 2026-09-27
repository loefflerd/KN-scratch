import Mathlib
import Definitions.FLT.Def_ModularCurve_ModuliPoint
import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.three_mul_natCard_moduliPoint_j_eq_zero_eq_dedekindPsi_add_two_mul_nuThree
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [DecidableEq L] [Algebra ℚ L] [IsAlgClosed L] :
    3 * Nat.card {x : ModuliPoint N L // ModuliPoint.j x = (0 : L)} = dedekindPsi N + 2 * nuThree N := by sorry
