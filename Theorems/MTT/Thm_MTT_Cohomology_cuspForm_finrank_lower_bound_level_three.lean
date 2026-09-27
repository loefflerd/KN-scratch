import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
theorem MTT.Cohomology.cuspForm_finrank_lower_bound_level_three {k : ℕ}
    (hk : 3 ≤ k) :
    k / 3 - 1 ≤ Module.finrank ℂ (CuspForm (MTT.GammaOne 3) (k : ℤ)) := by sorry
