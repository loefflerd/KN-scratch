import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
noncomputable section

theorem MTT.Cohomology.parabolicH1_finrank_le_level_one {k : ℕ} (hk : 2 ≤ k) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 1 (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne 1) (k : ℤ)) := by sorry
