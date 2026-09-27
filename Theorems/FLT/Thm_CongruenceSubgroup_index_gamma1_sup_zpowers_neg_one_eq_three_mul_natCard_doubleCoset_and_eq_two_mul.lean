import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem CongruenceSubgroup.index_gamma1_sup_zpowers_neg_one_eq_three_mul_natCard_doubleCoset_and_eq_two_mul
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) :
    (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
        3 * Nat.card (DoubleCoset.Quotient
          (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
          (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set SL(2, ℤ))) ∧
      (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
        2 * Nat.card (DoubleCoset.Quotient
          (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
          (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ))) := by sorry
