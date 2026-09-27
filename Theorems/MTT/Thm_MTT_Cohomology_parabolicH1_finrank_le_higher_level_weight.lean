import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
set_option autoImplicit false
noncomputable section

theorem MTT.Cohomology.parabolicH1_finrank_le_higher_level_weight {N k : ℕ}
    (hN : 2 ≤ N) (hk : 3 ≤ k) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) := by sorry
