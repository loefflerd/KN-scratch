import Definitions.MTT.Def_MTT_PeriodPairing
import Mathlib.NumberTheory.ModularForms.Bounds

set_option autoImplicit false
noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology
theorem MTT.Cohomology.mixed_period_test_functions_local_equivariant
    {N k : ℕ} (hk : 2 ≤ k)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U) :
    let A₁ : ℂ → ℂ := fun z =>
      periodContraction (k - 2) (U z)
        (conj ((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) (conj z))
    let A₂ : ℂ → ℂ := fun z => conj <|
      periodContraction (k - 2)
        (((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) z) (U z)
    ContDiffOn ℝ 1 A₁ upperHalfPlaneSet ∧
    (∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ,
      A₁ ((γ • τ : ℍ) : ℂ) =
        (starRingEnd ℂ (denom γ τ)) ^ 2 * A₁ τ) ∧
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
    (∀ z : ℍ,
      (1 / 2 : ℂ) *
          (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I) =
        -conj (periodContraction (k - 2)
          (q z • periodPower (k - 2) (z : ℂ))
          (conj (v z) • periodPower (k - 2) (conj (z : ℂ))))) := by sorry
