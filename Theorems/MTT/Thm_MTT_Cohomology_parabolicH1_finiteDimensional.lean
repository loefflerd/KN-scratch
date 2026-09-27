import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
set_option autoImplicit false
noncomputable section

theorem MTT.Cohomology.parabolicH1_finiteDimensional {N n : ℕ} (hN : 0 < N) :
    FiniteDimensional ℂ (MTT.Cohomology.ParabolicH1 N n) := by sorry
