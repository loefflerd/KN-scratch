import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.NumberTheory.ModularForms.QExpansion
open UpperHalfPlane
theorem MTT.Cohomology.exists_weighted_cusp_seeds_level_four :
    ∃ A : ModularForm (MTT.GammaOne 4) 1,
      ∃ B : ModularForm (MTT.GammaOne 4) 2,
        ∃ D : CuspForm (MTT.GammaOne 4) 5,
          (qExpansion 1 A).order = 0 ∧ (qExpansion 1 B).order = 1 ∧ D ≠ 0 := by sorry
