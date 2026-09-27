import Mathlib
import Definitions.FLT.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
open scoped MatrixGroups ModularForm
theorem ModularCurve.eventually_norm_slash_le_mul_of_isIntegral_adjoin_jqModC_inv_sq
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) {k : ℤ} (m : ℕ) (hm : 1 ≤ m)
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) (X : LaurentSeries ℂ)
    (hX : X * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (h₂ : IsIntegral (Algebra.adjoin ℂ ({(ModularCurve.jqModC ℂ)⁻¹} : Set (LaurentSeries ℂ)))
      (X ^ 2 * ModularCurve.jqModC ℂ ^ m * (ModularCurve.jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ m))
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ C : ℝ, ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty,
      ‖((fun z : UpperHalfPlane => g z * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) ^ m) ∣[k + 14 * (m : ℤ)] (A : GL (Fin 2) ℝ)) τ‖ ≤
        C * ‖((fun z : UpperHalfPlane => h z * ModularForm.discriminant z ^ m) ∣[k + 12 * (m : ℤ)] (A : GL (Fin 2) ℝ)) τ‖ := by sorry
