import Mathlib
import Definitions.FLT.Def_ModularCurve_X1
import Definitions.FLT.Def_ModularCurve_JqCoeff
import Definitions.FLT.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup
open ModularCurve
open AlgebraicCurve
open scoped MatrixGroups
theorem ModularCurve.twelve_mul_genusFF_laurentBaseChange_gamma1_add_six_mul_natCard_doubleCoset_eq_index_add_twelve_of_isAlgClosed
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) :
    12 * AlgebraicCurve.genusFF K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) +
      6 * Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) =
      (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index + 12 := by sorry
