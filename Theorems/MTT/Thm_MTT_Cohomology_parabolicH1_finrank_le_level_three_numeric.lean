import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
theorem MTT.Cohomology.parabolicH1_finrank_le_level_three_numeric {n : ℕ}
    (hn : 0 < n) (hno : Odd n) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 3 n) ≤ 2 * ((n + 2) / 3 - 1) := by sorry
