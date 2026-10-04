import Mathlib
import Definitions.FLT.Def_ModularCurve_X1
import Definitions.FLT.Def_ModularCurve_JqCoeff
import Definitions.FLT.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup AlgebraicCurve
open ModularCurve
open scoped MatrixGroups
theorem ModularCurve.natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (M : ℕ) [NeZero M]
    (y : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hy : (y : LaurentSeries K) = ModularCurve.jqModC K) :
    Nat.card {P : AlgebraicCurve.Place K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) // P.ord y < 0} =
      Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) := by sorry
