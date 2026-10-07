module

public import Definitions.MTT.Def_MTT_ParabolicCohomology
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le_levels_three_four_even
import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le_levels_three_four_odd

section privateSection

theorem solution {N k : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 4) (hk : 3 ≤ k) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) := by
  rcases Nat.even_or_odd k with hke | hko
  · exact MTT.Cohomology.parabolicH1_finrank_le_levels_three_four_even hN hN' hk hke
  · exact MTT.Cohomology.parabolicH1_finrank_le_levels_three_four_odd hN hN' hk hko

end privateSection

public section publicSection

theorem MTT.Cohomology.parabolicH1_finrank_le_levels_three_four {N k : ℕ}
    (hN : 3 ≤ N) (hN' : N ≤ 4) (hk : 3 ≤ k) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) := _root_.solution hN hN' hk

end publicSection
