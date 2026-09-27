import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
set_option autoImplicit false
noncomputable section

theorem MTT.Cohomology.parabolicH1_finrank_le_weight_two {N : ℕ} (hN : 0 < N) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N 0) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) 2) := by sorry
