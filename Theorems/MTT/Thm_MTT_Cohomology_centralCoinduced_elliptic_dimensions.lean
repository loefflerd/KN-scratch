import Definitions.MTT.Def_MTT_FullParabolicCohomology
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
open scoped MatrixGroups
theorem MTT.Cohomology.centralCoinduced_elliptic_dimensions {N n : ℕ} (hN : 5 ≤ N) :
    Module.finrank ℂ (centralCoinduced N n) =
        (n + 1) * (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ∧
      2 * Module.finrank ℂ ((centralCoinduced N n).ρ ModularGroup.S - LinearMap.id).ker =
        Module.finrank ℂ (centralCoinduced N n) ∧
      3 * Module.finrank ℂ
        ((centralCoinduced N n).ρ (ModularGroup.S * ModularGroup.T) - LinearMap.id).ker =
        Module.finrank ℂ (centralCoinduced N n) := by sorry
