import Mathlib.NumberTheory.ModularForms.Discriminant

import Definitions.FLT.Def_ModularCurve_LaurentCoeff
import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
open scoped MatrixGroups ModularForm
theorem ModularCurve.eventually_norm_slash_le_of_isIntegral_adjoin_coeffEmb_jq_inv_pow (N : ℕ) {k : ℤ} (m : ℕ)
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (X : LaurentSeries ℂ)
    (hX : X * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (M : ℕ)
    (h₂ : IsIntegral (Algebra.adjoin ℂ ({(ModularCurve.coeffEmb ℂ ModularCurve.jq)⁻¹} : Set (LaurentSeries ℂ)))
      (X ^ (2 * M) * ModularCurve.coeffEmb ℂ ModularCurve.jq ^ (m * M + 1) * (ModularCurve.coeffEmb ℂ ModularCurve.jq - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (m * M)))
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty,
      ‖((fun z : UpperHalfPlane => g z * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) ^ m) ∣[k + 14 * (m : ℤ)] (A : GL (Fin 2) ℝ)) τ‖ ≤
        ε * ‖((fun z : UpperHalfPlane => h z * ModularForm.discriminant z ^ m) ∣[k + 12 * (m : ℤ)] (A : GL (Fin 2) ℝ)) τ‖ := by sorry
