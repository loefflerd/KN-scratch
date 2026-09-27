import Definitions.MTT.Def_MTT_FullParabolicCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

theorem MTT.Cohomology.parabolicH1_finrank_le_centralCoinduced {N n : ℕ} (hN : 0 < N) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N n) ≤
      Module.finrank ℂ (MTT.Cohomology.FullParabolicH1
        (MTT.Cohomology.centralCoinduced N n)) := by sorry
