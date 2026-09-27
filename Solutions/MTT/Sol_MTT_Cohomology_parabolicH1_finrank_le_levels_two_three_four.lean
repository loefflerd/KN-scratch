import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le_level_two
import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le_levels_three_four

/-! # Removing the proved level-two case from the small-level frontier -/

theorem solution {N k : ℕ} (hN : 2 ≤ N) (hN' : N ≤ 4) (hk : 3 ≤ k) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) := by
  by_cases h₂ : N = 2
  · subst N
    exact MTT.Cohomology.parabolicH1_finrank_le_level_two (by omega)
  · exact MTT.Cohomology.parabolicH1_finrank_le_levels_three_four (by omega) hN' hk
