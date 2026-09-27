import Mathlib
open scoped MatrixGroups

theorem MTT.Cohomology.gammaOne_cuspForm_dimension_lower_bound {N k : ℕ} (hN : 5 ≤ N) (hk : 3 ≤ k) :
    (k - 1) * (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      12 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ)) +
        6 * Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
          ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
            Set SL(2, ℤ))) := by sorry
