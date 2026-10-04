/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Theorems.MTT.Thm_MTT_Cohomology_periodDensity_integrableOn_tile
import Theorems.MTT.Thm_MTT_Cohomology_mixed_period_test_functions_local_equivariant
import Definitions.MTT.Def_MTT_PeriodPairing
import Mathlib.NumberTheory.ModularForms.Bounds

/-! # Reducing mixed-period integrability to the local calculus identities -/

noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U)
    (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    let A₁ : ℂ → ℂ := fun z =>
      periodContraction (k - 2) (U z)
        (conj ((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) (conj z))
    let A₂ : ℂ → ℂ := fun z => conj <|
      periodContraction (k - 2)
        (((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) z) (U z)
    (∀ σ ∈ R, IntegrableOn
      (fun z ↦ (1 / 2 : ℂ) *
        (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I))
      ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume) ∧
    (∀ σ ∈ R, IntegrableOn
      (fun z ↦ (1 / 2 : ℂ) *
        (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I))
      ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume) := by
  intro A₁ A₂
  have h := mixed_period_test_functions_local_equivariant hk g v q U hU
  constructor
  · intro σ _
    exact periodDensity_integrableOn_tile hN hk g q σ _ h.2.2.1
  · intro σ _
    have hi := periodDensity_integrableOn_tile hN hk q v σ
      (fun z => -conj ((1 / 2 : ℂ) *
        (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I)))
      (fun z => by rw [h.2.2.2.2.2]; simp)
    simpa [IntegrableOn, sub_eq_add_neg] using
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hi).neg
