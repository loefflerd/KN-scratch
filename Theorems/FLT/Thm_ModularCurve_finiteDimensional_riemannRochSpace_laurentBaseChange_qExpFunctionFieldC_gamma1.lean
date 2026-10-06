import Definitions.FLT.Def_AlgebraicCurve_Repartitions
import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve CongruenceSubgroup
open AlgebraicCurve
open scoped MatrixGroups
theorem ModularCurve.finiteDimensional_riemannRochSpace_laurentBaseChange_qExpFunctionFieldC_gamma1
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K] (M : ℕ) [NeZero M]
    (D : AlgebraicCurve.Divisor K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) :
    FiniteDimensional K ↥(AlgebraicCurve.riemannRochSpace D) := by sorry
