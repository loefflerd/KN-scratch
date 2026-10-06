module

public import Definitions.MTT.Def_MTT_PeriodPairing
public import Mathlib.NumberTheory.ModularForms.Bounds

import Theorems.MTT.Thm_MTT_Cohomology_periodPairing_eq_sum_tiles

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

section privateSection

/-! # The corrected finite-transversal comparison -/

noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology

set_option linter.unusedVariables false in
theorem solution
    {N k : ℕ} (hk : 2 ≤ k)
    (f q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hR : Subgroup.IsComplement
      (CongruenceSubgroup.Gamma1 N : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
      (R : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)))
    (D : ℂ → ℂ)
    (hint : ∀ σ ∈ R, IntegrableOn D
      ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume)
    (hD : ∀ z : ℍ, D z =
      periodContraction (k - 2)
        (f z • periodPower (k - 2) (z : ℂ))
        (conj (q z) • periodPower (k - 2) (conj (z : ℂ)))) :
    periodPairing N (k - 2) f q =
      ∑ σ ∈ R, ∫ z in (fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟, D z := by
  exact periodPairing_eq_sum_tiles hk f q R hR D hD
end

end privateSection

public section publicSection

noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology
theorem MTT.Cohomology.periodPairing_eq_transversal_integral_of_weight_ge_two
    {N k : ℕ} (hk : 2 ≤ k)
    (f q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hR : Subgroup.IsComplement
      (CongruenceSubgroup.Gamma1 N : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
      (R : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)))
    (D : ℂ → ℂ)
    (hint : ∀ σ ∈ R, IntegrableOn D
      ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume)
    (hD : ∀ z : ℍ, D z =
      periodContraction (k - 2)
        (f z • periodPower (k - 2) (z : ℂ))
        (conj (q z) • periodPower (k - 2) (conj (z : ℂ)))) :
    periodPairing N (k - 2) f q =
      ∑ σ ∈ R, ∫ z in (fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟, D z := _root_.solution hk f q R hR D hint hD
end

end publicSection
