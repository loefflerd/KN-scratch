import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

theorem MTT.Cohomology.parabolicH1_finrank_le_level_two {k : ℕ} (hk : 2 ≤ k) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 2 (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne 2) (k : ℤ)) := by sorry
