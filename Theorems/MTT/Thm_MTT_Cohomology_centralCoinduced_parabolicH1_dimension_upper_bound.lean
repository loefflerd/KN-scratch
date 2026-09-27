import Definitions.MTT.Def_MTT_FullParabolicCohomology
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
open scoped MatrixGroups


theorem MTT.Cohomology.centralCoinduced_parabolicH1_dimension_upper_bound {N k : ℕ}
    (hN : 5 ≤ N) (hk : 3 ≤ k) :
    6 * Module.finrank ℂ (MTT.Cohomology.FullParabolicH1 (MTT.Cohomology.centralCoinduced N (k - 2))) +
        6 * Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
          ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
            Set SL(2, ℤ))) ≤
      (k - 1) * (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by sorry
