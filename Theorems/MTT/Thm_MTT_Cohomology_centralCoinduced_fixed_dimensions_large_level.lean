module

public import Definitions.MTT.Def_MTT_FullParabolicCohomology
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Theorems.MTT.Thm_MTT_Cohomology_centralCoinduced_elliptic_dimensions
import Theorems.MTT.Thm_MTT_Cohomology_centralCoinduced_T_fixed_cusp_lower_bound

section privateSection

open scoped MatrixGroups

theorem solution {N n : ℕ} (hN : 5 ≤ N) (hn : 0 < n) :
    let W := MTT.Cohomology.centralCoinduced N n
    Module.finrank ℂ W =
        (n + 1) * (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ∧
      2 * Module.finrank ℂ (W.ρ ModularGroup.S - LinearMap.id).ker = Module.finrank ℂ W ∧
      3 * Module.finrank ℂ (W.ρ (ModularGroup.S * ModularGroup.T) - LinearMap.id).ker =
        Module.finrank ℂ W ∧
      Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
          Set SL(2, ℤ))) ≤ Module.finrank ℂ (W.ρ ModularGroup.T - LinearMap.id).ker := by
  obtain ⟨hd, hS, hU⟩ := MTT.Cohomology.centralCoinduced_elliptic_dimensions (n := n) hN
  exact ⟨hd, hS, hU, MTT.Cohomology.centralCoinduced_T_fixed_cusp_lower_bound hN hn⟩

end privateSection

public section publicSection

open scoped MatrixGroups

theorem MTT.Cohomology.centralCoinduced_fixed_dimensions_large_level {N n : ℕ}
    (hN : 5 ≤ N) (hn : 0 < n) :
    let W := MTT.Cohomology.centralCoinduced N n
    Module.finrank ℂ W =
        (n + 1) * (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ∧
      2 * Module.finrank ℂ (W.ρ ModularGroup.S - LinearMap.id).ker = Module.finrank ℂ W ∧
      3 * Module.finrank ℂ (W.ρ (ModularGroup.S * ModularGroup.T) - LinearMap.id).ker =
        Module.finrank ℂ W ∧
      Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
          Set SL(2, ℤ))) ≤ Module.finrank ℂ (W.ρ ModularGroup.T - LinearMap.id).ker := _root_.solution hN hn

end publicSection
