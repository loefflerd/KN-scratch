import Definitions.MTT.Def_MTT_Arithmetic
import Mathlib.NumberTheory.ModularForms.QExpansion

theorem MTT.Cohomology.exists_weighted_modular_seeds_level_four :
    ∃ A : ModularForm (MTT.GammaOne 4) 1,
      ∃ B : ModularForm (MTT.GammaOne 4) 2,
        MvPowerSeries.order (UpperHalfPlane.qExpansion 1 A) = 0 ∧
          MvPowerSeries.order (UpperHalfPlane.qExpansion 1 B) = 1 := by sorry
