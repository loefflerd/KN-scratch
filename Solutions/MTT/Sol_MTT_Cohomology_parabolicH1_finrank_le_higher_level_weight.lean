import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_dimension_upper_bound_large_level
import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le_levels_two_three_four
import Theorems.MTT.Thm_MTT_Cohomology_gammaOne_cuspForm_dimension_lower_bound

noncomputable section

theorem solution {N k : ℕ} (hN : 2 ≤ N) (hk : 3 ≤ k) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) := by
  by_cases hlarge : 5 ≤ N
  · have hu := MTT.Cohomology.parabolicH1_dimension_upper_bound_large_level hlarge hk
    have hl := MTT.Cohomology.gammaOne_cuspForm_dimension_lower_bound hlarge hk
    change _ ≤ 12 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) + _ at hl
    omega
  · exact MTT.Cohomology.parabolicH1_finrank_le_levels_two_three_four hN (by omega) hk
