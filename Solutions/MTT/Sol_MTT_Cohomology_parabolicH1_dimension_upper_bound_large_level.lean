import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le_centralCoinduced
import Theorems.MTT.Thm_MTT_Cohomology_centralCoinduced_parabolicH1_dimension_upper_bound

/-! # Reduction to the full-group central-fixed coefficient count -/

open scoped MatrixGroups

theorem solution {N k : ℕ} (hN : 5 ≤ N) (hk : 3 ≤ k) :
    6 * Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N (k - 2)) +
        6 * Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
          ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
            Set SL(2, ℤ))) ≤
      (k - 1) * (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  have hcomp := MTT.Cohomology.parabolicH1_finrank_le_centralCoinduced
    (n := k - 2) (show 0 < N by omega)
  have hcount := MTT.Cohomology.centralCoinduced_parabolicH1_dimension_upper_bound hN hk
  omega
