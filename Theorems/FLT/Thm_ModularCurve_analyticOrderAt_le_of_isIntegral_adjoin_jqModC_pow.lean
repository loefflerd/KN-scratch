import Mathlib.NumberTheory.ModularForms.Discriminant

import Definitions.FLT.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
open scoped MatrixGroups ModularForm
theorem ModularCurve.analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) {k : ℤ} (m : ℕ)
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (X : LaurentSeries ℂ)
    (hX : X * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (h₁ : IsIntegral (Algebra.adjoin ℂ ({ModularCurve.jqModC ℂ} : Set (LaurentSeries ℂ)))
      (X ^ 6 * ModularCurve.jqModC ℂ ^ (4 * m) * (ModularCurve.jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * m)))
    (τ : UpperHalfPlane) :
    analyticOrderAt ((fun z : UpperHalfPlane => h z * ModularForm.discriminant z ^ m) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ≤
      analyticOrderAt ((fun z : UpperHalfPlane => g z * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) ^ m) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) := by sorry
