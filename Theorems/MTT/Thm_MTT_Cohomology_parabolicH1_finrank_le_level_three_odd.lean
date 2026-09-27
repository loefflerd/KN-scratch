import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
theorem MTT.Cohomology.parabolicH1_finrank_le_level_three_odd {k : ℕ}
    (hk : 3 ≤ k) (hko : Odd k) :
    Module.finrank ℂ (ParabolicH1 3 (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne 3) (k : ℤ)) := by sorry
