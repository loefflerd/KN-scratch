import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Geometry.Manifold.Notation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Complex Real
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold
theorem ModularForm.weierstrassP_torsion_qExpansion_package
    (N : ℕ) (hN : N ≠ 0) (L : ℍ → PeriodPair)
    (hL : ∀ τ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) :
    let ζ : ℂ := Complex.exp (2 * π * I / N)
    let k : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {ζ}
    let ζk : k := IntermediateField.AdjoinSimple.gen ℚ ζ
    let W : ℕ → ℕ → ℍ → ℂ := fun a₁ a₂ τ ↦ ((2 * π * I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) (((a₁ : ℂ) * (τ : ℂ) + (a₂ : ℂ)) / (N : ℂ))

    (∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (W a₁ a₂)
        ∧ Function.Periodic ((W a₁ a₂) ∘ UpperHalfPlane.ofComplex) (N : ℂ)
        ∧ IsBoundedAtImInfty (W a₁ a₂)
        ∧ ∀ n, (qExpansion N (W a₁ a₂)).coeff n ∈ k)

    ∧ (∀ a₁ a₂ b₁ b₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
        b₁ < N → b₂ < N → (b₁ ≠ 0 ∨ b₂ ≠ 0) →
        W a₁ a₂ = W b₁ b₂ →
        (b₁ = a₁ ∧ b₂ = a₂) ∨ (b₁ = (N - a₁) % N ∧ b₂ = (N - a₂) % N))

    ∧ (∃ S : ℕ → ℕ → PowerSeries k,
        (∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
          (S a₁ a₂).map (algebraMap k ℂ) = qExpansion N (W a₁ a₂))
        ∧ ∀ s : ℕ, s.Coprime N → ∀ φ : k →+* ℂ, φ ζk = ζ ^ s →
            ∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
              (S a₁ a₂).map φ = qExpansion N (W a₁ (s * a₂ % N)))

    ∧ (∀ f : ℍ → ℂ, Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℂ) →
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → IsBoundedAtImInfty f →
        ∀ n, (qExpansion N f).coeff n =
          if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0)

    ∧ (∀ n, ∃ q : ℚ, (qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff n = (q : ℂ))
    ∧ (∀ n, ∃ q : ℚ, (qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ)).coeff n = (q : ℂ))
    ∧ (∀ n, ∃ q : ℚ,
        (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff n = (q : ℂ)) := by sorry
