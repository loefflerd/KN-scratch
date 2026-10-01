import Definitions.FLT.Def_ModularCurve_GenusNumerics
import Definitions.FLT.Def_ModularCurve_ModuliPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [DecidableEq L] [Algebra ℚ L] [IsAlgClosed L] :
    2 * Nat.card {x : ModuliPoint N L // ModuliPoint.j x = (1728 : L)} = dedekindPsi N + nuTwo N := by sorry
