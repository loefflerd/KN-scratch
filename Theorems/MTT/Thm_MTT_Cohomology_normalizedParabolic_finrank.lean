import Definitions.MTT.Def_MTT_NormalizedParabolicCocycles
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
set_option autoImplicit false
noncomputable section

theorem MTT.Cohomology.normalizedParabolic_finrank {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    Module.finrank ℂ (MTT.Cohomology.normalizedParabolic N n) =
      Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N n) + 1 := by sorry
