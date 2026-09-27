import Definitions.MTT.Def_MTT_FullParabolicCohomology
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
          Set SL(2, ℤ))) ≤ Module.finrank ℂ (W.ρ ModularGroup.T - LinearMap.id).ker := by sorry
