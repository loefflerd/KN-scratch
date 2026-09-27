import Theorems.MTT.Thm_CuspForm_finrank_lower_bound_of_weighted_forms
import Theorems.MTT.Thm_MTT_Cohomology_exists_weighted_cusp_seeds_level_four
import Theorems.FLT.Thm_ModularForm_finiteDimensional_of_isArithmetic
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.Tactic

open UpperHalfPlane

theorem solution {k : ℕ} (hk : 3 ≤ k) (hko : Odd k) :
    k - 3 ≤ 2 * Module.finrank ℂ (CuspForm (MTT.GammaOne 4) (k : ℤ)) := by
  by_cases hr : 5 ≤ k
  · obtain ⟨A, B, D, hA, hB, hD⟩ := MTT.Cohomology.exists_weighted_cusp_seeds_level_four
    have := ModularForm.finiteDimensional_of_isArithmetic (MTT.GammaOne 4) (k : ℤ)
    have : FiniteDimensional ℂ (CuspForm (MTT.GammaOne 4) (k : ℤ)) :=
      FiniteDimensional.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective
    have hΓ : (1 : ℝ) ∈ (MTT.GammaOne 4).strictPeriods := by
      change (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 4 : Subgroup (GL (Fin 2) ℝ)).strictPeriods
      rw [CongruenceSubgroup.strictPeriods_Gamma1]
      exact AddSubgroup.mem_zmultiples 1
    have hd := CuspForm.finrank_lower_bound_of_weighted_forms
      (by decide : 0 < 2) hr A B D 1 (by norm_num) hΓ hA hB hD
    obtain ⟨m, hm⟩ := hko
    omega
  · obtain ⟨m, hm⟩ := hko
    have : k - 3 = 0 := by omega
    rw [this]
    exact Nat.zero_le _
