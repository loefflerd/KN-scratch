import Definitions.MTT.Def_MTT_FullParabolicCohomology
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
open scoped MatrixGroups
theorem MTT.Cohomology.centralCoinduced_T_fixed_cusp_lower_bound {N n : ℕ}
    (hN : 5 ≤ N) (hn : 0 < n) :
    Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
      ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
        Set SL(2, ℤ))) ≤
      Module.finrank ℂ ((MTT.Cohomology.centralCoinduced N n).ρ ModularGroup.T -
        LinearMap.id).ker := by sorry
