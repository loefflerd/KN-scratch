import Definitions.FLT.Def_ModularCurve_JqCoeff
import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve CongruenceSubgroup AlgebraicCurve
open scoped MatrixGroups
theorem ModularCurve.ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (M : ℕ) [NeZero M] (hM : 4 ≤ M)
    (y : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hy : (y : LaurentSeries K) = ModularCurve.jqModC K) :
    (∀ P : AlgebraicCurve.Place K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))), 0 < P.ord y → P.ord y = 3) ∧
      (∀ P : AlgebraicCurve.Place K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))), 0 < P.ord (y - 1728) → P.ord (y - 1728) = 2) := by sorry
