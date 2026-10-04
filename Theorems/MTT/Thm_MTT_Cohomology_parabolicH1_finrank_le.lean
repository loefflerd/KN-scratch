import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
noncomputable section

theorem MTT.Cohomology.parabolicH1_finrank_le {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) := by sorry
