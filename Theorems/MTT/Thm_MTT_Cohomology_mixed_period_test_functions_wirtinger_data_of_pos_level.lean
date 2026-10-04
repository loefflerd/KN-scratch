import Definitions.MTT.Def_MTT_PeriodPairing
import Mathlib.NumberTheory.ModularForms.Bounds

noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology
theorem MTT.Cohomology.mixed_period_test_functions_wirtinger_data_of_pos_level
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U)
    (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    ∃ A₁ A₂ : ℂ → ℂ,
      ContDiffOn ℝ 1 A₁ upperHalfPlaneSet ∧
      (∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ,
        A₁ ((γ • τ : ℍ) : ℂ) =
          (starRingEnd ℂ (denom γ τ)) ^ 2 * A₁ τ) ∧
      (∀ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, IsZeroAtImInfty
        fun τ : ℍ ↦ A₁ ((σ • τ : ℍ) : ℂ) *
          ((starRingEnd ℂ (denom σ τ)) ^ 2)⁻¹) ∧
      (∀ σ ∈ R, IntegrableOn
        (fun z ↦ (1 / 2 : ℂ) *
          (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I))
        ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume) ∧
      (∀ z : ℍ,
        (1 / 2 : ℂ) *
            (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I) =
          periodContraction (k - 2)
            (g z • periodPower (k - 2) (z : ℂ))
            (conj (q z) • periodPower (k - 2) (conj (z : ℂ)))) ∧
      ContDiffOn ℝ 1 A₂ upperHalfPlaneSet ∧
      (∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ,
        A₂ ((γ • τ : ℍ) : ℂ) =
          (starRingEnd ℂ (denom γ τ)) ^ 2 * A₂ τ) ∧
      (∀ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, IsZeroAtImInfty
        fun τ : ℍ ↦ A₂ ((σ • τ : ℍ) : ℂ) *
          ((starRingEnd ℂ (denom σ τ)) ^ 2)⁻¹) ∧
      (∀ σ ∈ R, IntegrableOn
        (fun z ↦ (1 / 2 : ℂ) *
          (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I))
        ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume) ∧
      (∀ z : ℍ,
        (1 / 2 : ℂ) *
            (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I) =
          -conj (periodContraction (k - 2)
            (q z • periodPower (k - 2) (z : ℂ))
            (conj (v z) • periodPower (k - 2) (conj (z : ℂ))))) := by sorry
