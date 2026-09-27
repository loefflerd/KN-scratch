import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.NumberTheory.ModularForms.QExpansion
open UpperHalfPlane
theorem MTT.Cohomology.exists_weighted_cusp_seeds_level_three :
    ∃ A : ModularForm (MTT.GammaOne 3) 1,
      ∃ B : ModularForm (MTT.GammaOne 3) 3,
        ∃ D : CuspForm (MTT.GammaOne 3) 6,
          (qExpansion 1 A).order = 0 ∧ (qExpansion 1 B).order = 1 ∧ D ≠ 0 := by sorry
