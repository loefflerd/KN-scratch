import Theorems.MTT.Thm_MTT_Cohomology_exists_weighted_modular_seeds_level_four
import Theorems.MTT.Thm_MTT_Cohomology_exists_nonzero_cuspForm_weight_five_level_four

theorem solution :
    ∃ A : ModularForm (MTT.GammaOne 4) 1,
      ∃ B : ModularForm (MTT.GammaOne 4) 2,
        ∃ D : CuspForm (MTT.GammaOne 4) 5,
          MvPowerSeries.order (UpperHalfPlane.qExpansion 1 A) = 0 ∧
            MvPowerSeries.order (UpperHalfPlane.qExpansion 1 B) = 1 ∧ D ≠ 0 := by
  obtain ⟨A, B, hA, hB⟩ := MTT.Cohomology.exists_weighted_modular_seeds_level_four
  obtain ⟨D, hD⟩ := MTT.Cohomology.exists_nonzero_cuspForm_weight_five_level_four
  exact ⟨A, B, D, hA, hB, hD⟩
