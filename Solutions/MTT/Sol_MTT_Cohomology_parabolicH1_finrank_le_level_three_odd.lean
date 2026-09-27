import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le_level_three_numeric
import Theorems.MTT.Thm_MTT_Cohomology_cuspForm_finrank_lower_bound_level_three
import Mathlib.Tactic

set_option autoImplicit false

open MTT.Cohomology

theorem solution {k : ℕ} (hk : 3 ≤ k) (hko : Odd k) :
    Module.finrank ℂ (ParabolicH1 3 (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne 3) (k : ℤ)) := by
  have hno : Odd (k - 2) := by
    obtain ⟨m, hm⟩ := hko
    exact ⟨m - 1, by omega⟩
  have hc := parabolicH1_finrank_le_level_three_numeric (by omega : 0 < k - 2) hno
  rw [show k - 2 + 2 = k by omega] at hc
  have hs := cuspForm_finrank_lower_bound_level_three hk
  omega
