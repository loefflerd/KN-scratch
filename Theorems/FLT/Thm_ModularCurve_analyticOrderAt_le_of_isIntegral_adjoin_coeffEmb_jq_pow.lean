import Mathlib
import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.analyticOrderAt_le_of_isIntegral_adjoin_coeffEmb_jq_pow (N : ℕ) {k : ℤ} (m : ℕ)
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (X : LaurentSeries ℂ)
    (hX : X * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (h₁ : IsIntegral (Algebra.adjoin ℂ ({ModularCurve.coeffEmb ℂ ModularCurve.jq} : Set (LaurentSeries ℂ)))
      (X ^ 6 * ModularCurve.coeffEmb ℂ ModularCurve.jq ^ (4 * m) * (ModularCurve.coeffEmb ℂ ModularCurve.jq - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * m)))
    (τ : UpperHalfPlane) :
    analyticOrderAt ((fun z : UpperHalfPlane => h z * ModularForm.discriminant z ^ m) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ≤
      analyticOrderAt ((fun z : UpperHalfPlane => g z * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) ^ m) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) := by sorry
