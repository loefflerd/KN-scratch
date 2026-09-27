import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
theorem MTT.Cohomology.cuspForm_finrank_lower_bound_level_four_odd {k : ℕ}
    (hk : 3 ≤ k) (hko : Odd k) :
    k - 3 ≤ 2 * Module.finrank ℂ (CuspForm (MTT.GammaOne 4) (k : ℤ)) := by sorry
