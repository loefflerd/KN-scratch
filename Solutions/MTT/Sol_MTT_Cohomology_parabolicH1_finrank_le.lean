import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le_level_one
import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le_weight_two
import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le_higher_level_weight
import Mathlib.Tactic

theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) := by
  by_cases hlevel : N = 1
  · subst N
    exact MTT.Cohomology.parabolicH1_finrank_le_level_one hk
  by_cases hweight : k = 2
  · subst k
    exact MTT.Cohomology.parabolicH1_finrank_le_weight_two hN
  exact MTT.Cohomology.parabolicH1_finrank_le_higher_level_weight (by omega) (by omega)
