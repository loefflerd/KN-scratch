import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.Notation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Complex Real Polynomial
open UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm
theorem WLight.levelOne_hauptmodul_package :

    (∀ (m : ℕ) (h : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
      (∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h) →
      IsBoundedAtImInfty (h * ModularForm.discriminant ^ m) →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
        h = fun τ => Polynomial.eval (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) P) ∧

    (∀ (k : IntermediateField ℚ ℂ) (N : ℕ), N ≠ 0 → ∀ (m : ℕ) (h : ℍ → ℂ),
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
      (∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h) →
      Function.Periodic ((h * ModularForm.discriminant ^ m) ∘ ofComplex) N →
      IsBoundedAtImInfty (h * ModularForm.discriminant ^ m) →
      (∀ n : ℕ, (qExpansion N (h * ModularForm.discriminant ^ m)).coeff n ∈ k) →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧ (∀ i, P.coeff i ∈ k) ∧
        h = fun τ => Polynomial.eval (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) P) ∧

    Function.Surjective (fun τ : ℍ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) ∧

    (∀ (m : ℕ) (P : Polynomial ℂ), P.natDegree ≤ m →
      (∀ n : ℕ, ∃ q : ℚ, (∑ i ∈ Finset.range (m + 1),
          PowerSeries.C (P.coeff i) * qExpansion 1 ⇑ModularForm.E₄ ^ (3 * i) *
            qExpansion 1 ModularForm.discriminant ^ (m - i)).coeff n = (q : ℂ)) →
      ∀ i : ℕ, ∃ q : ℚ, P.coeff i = (q : ℂ)) ∧

    (∀ (k : IntermediateField ℚ ℂ) (m : ℕ) (P : Polynomial ℂ), P.natDegree ≤ m →
      (∀ n : ℕ, (∑ i ∈ Finset.range (m + 1),
          PowerSeries.C (P.coeff i) * qExpansion 1 ⇑ModularForm.E₄ ^ (3 * i) *
            qExpansion 1 ModularForm.discriminant ^ (m - i)).coeff n ∈ k) →
      ∀ i : ℕ, P.coeff i ∈ k) := by sorry
