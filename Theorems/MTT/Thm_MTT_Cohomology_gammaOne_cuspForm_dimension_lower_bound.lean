module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.NumberTheory.ModularForms.Basic

import Theorems.MTT.Thm_MTT_Cohomology_finrank_modularForm_le_cuspForm_add_doubleCosets
import Theorems.FLT.Thm_ModularForm_finiteDimensional_of_isArithmetic
import Theorems.FLT.Thm_ModularForm_exists_linearIndependent_gamma1_dimFormula_le_card

section privateSection

noncomputable section

open scoped MatrixGroups

theorem solution {N k : ℕ} (hN : 5 ≤ N) (hk : 3 ≤ k) :
    (k - 1) * (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      12 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ)) +
        6 * Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
          ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
            Set SL(2, ℤ))) := by
  have : NeZero N := ⟨by omega⟩
  have := ModularForm.finiteDimensional_of_isArithmetic
    ((CongruenceSubgroup.Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) (k : ℤ)
  obtain ⟨d, f, hli, hd⟩ :=
    ModularForm.exists_linearIndependent_gamma1_dimFormula_le_card N hN k hk
  have hf : d ≤ Module.finrank ℂ (ModularForm (CongruenceSubgroup.Gamma1 N) (k : ℤ)) := by
    simpa only [Fintype.card_fin] using hli.fintype_card_le_finrank
  have hc := MTT.Cohomology.finrank_modularForm_le_cuspForm_add_doubleCosets
    (CongruenceSubgroup.Gamma1 N) (k : ℤ)
  omega
end

end privateSection

public section publicSection

open scoped MatrixGroups

theorem MTT.Cohomology.gammaOne_cuspForm_dimension_lower_bound {N k : ℕ} (hN : 5 ≤ N) (hk : 3 ≤ k) :
    (k - 1) * (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      12 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ)) +
        6 * Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
          ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
            Set SL(2, ℤ))) := _root_.solution hN hk

end publicSection
