module

public import Definitions.MTT.Def_MTT_ParabolicCohomology
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_add_one_le_level_four
import Theorems.MTT.Thm_MTT_Cohomology_cuspForm_finrank_lower_bound_level_four_odd
import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le_level_three_odd
import Mathlib.Tactic

section privateSection

open MTT.Cohomology

theorem solution {N k : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 4) (hk : 3 ≤ k) (hko : Odd k) :
    Module.finrank ℂ (ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) := by
  have h : N = 3 ∨ N = 4 := by omega
  rcases h with rfl | rfl
  · exact parabolicH1_finrank_le_level_three_odd hk hko
  · have hc := parabolicH1_finrank_add_one_le_level_four (by omega : 0 < k - 2)
    have hs := cuspForm_finrank_lower_bound_level_four_odd hk hko
    omega

end privateSection

public section publicSection

theorem MTT.Cohomology.parabolicH1_finrank_le_levels_three_four_odd {N k : ℕ}
    (hN : 3 ≤ N) (hN' : N ≤ 4) (hk : 3 ≤ k) (hko : Odd k) :
    Module.finrank ℂ (ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) := _root_.solution hN hN' hk hko

end publicSection
