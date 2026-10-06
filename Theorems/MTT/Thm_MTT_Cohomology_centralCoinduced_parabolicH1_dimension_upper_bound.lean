module

public import Definitions.MTT.Def_MTT_FullParabolicCohomology
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Theorems.MTT.Thm_MTT_Cohomology_centralCoinduced_parabolicH1_add_fixed_finrank_le
import Theorems.MTT.Thm_MTT_Cohomology_centralCoinduced_fixed_dimensions_large_level

section privateSection

/-! # Reduction of the cohomological count to finite-coset fixed dimensions -/

open scoped MatrixGroups

theorem solution {N k : ℕ} (hN : 5 ≤ N) (hk : 3 ≤ k) :
    6 * Module.finrank ℂ
        (MTT.Cohomology.FullParabolicH1 (MTT.Cohomology.centralCoinduced N (k - 2))) +
        6 * Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
          ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
            Set SL(2, ℤ))) ≤
      (k - 1) * (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  have hc := MTT.Cohomology.centralCoinduced_parabolicH1_add_fixed_finrank_le
    (show 0 < N by omega) (show 0 < k - 2 by omega)
  obtain ⟨hd, hS, hU, hT⟩ :=
    MTT.Cohomology.centralCoinduced_fixed_dimensions_large_level hN
      (show 0 < k - 2 by omega)
  have hw : k - 2 + 1 = k - 1 := by omega
  rw [hw] at hd
  omega

end privateSection

public section publicSection

open scoped MatrixGroups


theorem MTT.Cohomology.centralCoinduced_parabolicH1_dimension_upper_bound {N k : ℕ}
    (hN : 5 ≤ N) (hk : 3 ≤ k) :
    6 * Module.finrank ℂ (MTT.Cohomology.FullParabolicH1 (MTT.Cohomology.centralCoinduced N (k - 2))) +
        6 * Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
          ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
            Set SL(2, ℤ))) ≤
      (k - 1) * (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := _root_.solution hN hk

end publicSection
