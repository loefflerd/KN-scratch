import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
theorem MTT.Cohomology.parabolicH1_finrank_le_levels_three_four_even {N k : ℕ}
    (hN : 3 ≤ N) (hN' : N ≤ 4) (hk : 3 ≤ k) (hke : Even k) :
    Module.finrank ℂ (ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) := by sorry
