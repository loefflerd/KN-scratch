import Mathlib.NumberTheory.ModularForms.Derivative

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.exists_rankinCohen_one_qExpansion_eq
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    {k₁ k₂ : ℤ} (g : ModularForm Γ k₁) (h : ModularForm Γ k₂) :
    ∃ B : ModularForm Γ (k₁ + k₂ + 2),
      (∀ τ : ℍ, B τ = k₁ * g τ * Derivative.normalizedDerivOfComplex h τ
                     - k₂ * Derivative.normalizedDerivOfComplex g τ * h τ) ∧
      qExpansion 1 (B : ℍ → ℂ) =
        PowerSeries.C (k₁ : ℂ) * qExpansion 1 (g : ℍ → ℂ) *
            PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 (h : ℍ → ℂ)).coeff n)
          - PowerSeries.C (k₂ : ℂ) *
            PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 (g : ℍ → ℂ)).coeff n) *
              qExpansion 1 (h : ℍ → ℂ) := by sorry
