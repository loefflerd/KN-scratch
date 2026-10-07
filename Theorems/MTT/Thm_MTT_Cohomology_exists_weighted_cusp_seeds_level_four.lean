module

public import Definitions.MTT.Def_MTT_ParabolicCohomology
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.RingTheory.MvPowerSeries.Order

import Theorems.MTT.Thm_MTT_Cohomology_exists_weighted_modular_seeds_level_four
import Theorems.MTT.Thm_MTT_Cohomology_exists_nonzero_cuspForm_weight_five_level_four

section privateSection

theorem solution :
    ∃ A : ModularForm (MTT.GammaOne 4) 1,
      ∃ B : ModularForm (MTT.GammaOne 4) 2,
        ∃ D : CuspForm (MTT.GammaOne 4) 5,
          MvPowerSeries.order (UpperHalfPlane.qExpansion 1 A) = 0 ∧
            MvPowerSeries.order (UpperHalfPlane.qExpansion 1 B) = 1 ∧ D ≠ 0 := by
  obtain ⟨A, B, hA, hB⟩ := MTT.Cohomology.exists_weighted_modular_seeds_level_four
  obtain ⟨D, hD⟩ := MTT.Cohomology.exists_nonzero_cuspForm_weight_five_level_four
  exact ⟨A, B, D, hA, hB, hD⟩

end privateSection

public section publicSection

open UpperHalfPlane
theorem MTT.Cohomology.exists_weighted_cusp_seeds_level_four :
    ∃ A : ModularForm (MTT.GammaOne 4) 1,
      ∃ B : ModularForm (MTT.GammaOne 4) 2,
        ∃ D : CuspForm (MTT.GammaOne 4) 5,
          MvPowerSeries.order (qExpansion 1 A) = 0 ∧
            MvPowerSeries.order (qExpansion 1 B) = 1 ∧ D ≠ 0 := _root_.solution

end publicSection
