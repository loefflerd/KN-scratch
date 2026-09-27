import Definitions.MTT.Def_MTT_FullParabolicCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

theorem MTT.Cohomology.centralCoinduced_parabolicH1_add_fixed_finrank_le {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    Module.finrank ℂ (MTT.Cohomology.FullParabolicH1 (MTT.Cohomology.centralCoinduced N n)) +
        Module.finrank ℂ ((MTT.Cohomology.centralCoinduced N n).ρ
          ModularGroup.S - LinearMap.id).ker +
        Module.finrank ℂ ((MTT.Cohomology.centralCoinduced N n).ρ
          (ModularGroup.S * ModularGroup.T) - LinearMap.id).ker +
        Module.finrank ℂ ((MTT.Cohomology.centralCoinduced N n).ρ
          ModularGroup.T - LinearMap.id).ker ≤
      Module.finrank ℂ (MTT.Cohomology.centralCoinduced N n) := by sorry
