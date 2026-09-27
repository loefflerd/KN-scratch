import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le_levels_three_four_even
import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le_levels_three_four_odd

theorem solution {N k : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 4) (hk : 3 ≤ k) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) := by
  rcases Nat.even_or_odd k with hke | hko
  · exact MTT.Cohomology.parabolicH1_finrank_le_levels_three_four_even hN hN' hk hke
  · exact MTT.Cohomology.parabolicH1_finrank_le_levels_three_four_odd hN hN' hk hko
