module

public import Definitions.MTT.Def_MTT_ParabolicCohomology
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.RingTheory.PowerSeries.Order
import Theorems.FLT.Thm_ModularForm_finiteDimensional_of_isArithmetic
import Theorems.MTT.Thm_CuspForm_finrank_lower_bound_of_weighted_forms
import Theorems.MTT.Thm_MTT_Cohomology_exists_weighted_cusp_seeds_level_three

section privateSection

open UpperHalfPlane

theorem solution {k : ℕ} (hk : 3 ≤ k) :
    k / 3 - 1 ≤ Module.finrank ℂ (CuspForm (MTT.GammaOne 3) (k : ℤ)) := by
  by_cases hr : 6 ≤ k
  · obtain ⟨A, B, D, hA, hB, hD⟩ := MTT.Cohomology.exists_weighted_cusp_seeds_level_three
    have := ModularForm.finiteDimensional_of_isArithmetic (MTT.GammaOne 3) (k : ℤ)
    have : FiniteDimensional ℂ (CuspForm (MTT.GammaOne 3) (k : ℤ)) :=
      FiniteDimensional.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective
    have hΓ : (1 : ℝ) ∈ (MTT.GammaOne 3).strictPeriods := by
      change (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 3 : Subgroup (GL (Fin 2) ℝ)).strictPeriods
      rw [CongruenceSubgroup.strictPeriods_Gamma1]
      exact AddSubgroup.mem_zmultiples 1
    have hd := CuspForm.finrank_lower_bound_of_weighted_forms
      (by decide : 0 < 3) hr A B D 1 (by norm_num) hΓ
      (PowerSeries.order_eq_order.trans hA) (PowerSeries.order_eq_order.trans hB) hD
    omega
  · have : k / 3 - 1 = 0 := by omega
    rw [this]
    exact Nat.zero_le _

end privateSection

public section publicSection

theorem MTT.Cohomology.cuspForm_finrank_lower_bound_level_three {k : ℕ}
    (hk : 3 ≤ k) :
    k / 3 - 1 ≤ Module.finrank ℂ (CuspForm (MTT.GammaOne 3) (k : ℤ)) := _root_.solution hk

end publicSection
