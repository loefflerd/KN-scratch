import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups
theorem ModularCurve.gammaFundamentalSet_boundary_sidePairing_of_slash_eq_add
    (Γ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Γ)]
    (φ ψ : ℍ → ℂ) (c : SL(2, ℤ) → ℂ)
    (hφ : ∀ γ ∈ Γ, ∀ τ : ℍ,
      φ (γ • τ) / denom (γ : GL (Fin 2) ℝ) τ ^ 2 = φ τ + c γ * ψ τ)
    (Φ Ψ : SL(2, ℤ) → ℂ → ℂ)
    (hΦ : ∀ (σ : SL(2, ℤ)) (z : ℂ),
      Φ σ z = φ (σ • ofComplex z) / denom (σ : GL (Fin 2) ℝ) (ofComplex z) ^ 2)
    (hΨ : ∀ (σ : SL(2, ℤ)) (z : ℂ),
      Ψ σ z = ψ (σ • ofComplex z) / denom (σ : GL (Fin 2) ℝ) (ofComplex z) ^ 2)
    (s : Set ℝ) (hs : MeasurableSet s) (hs0 : s ⊆ Set.Ioi 0)
    (hΦs : ∀ q : SL(2, ℤ) ⧸ Γ,
      IntegrableOn (fun y : ℝ => Φ (Quotient.out q)⁻¹ (-(1 / 2) + y * Complex.I)) s)
    (hΨs : ∀ q : SL(2, ℤ) ⧸ Γ,
      IntegrableOn (fun y : ℝ => Ψ (Quotient.out q)⁻¹ (-(1 / 2) + y * Complex.I)) s)
    (hΦarc : ∀ q : SL(2, ℤ) ⧸ Γ, IntervalIntegrable (fun θ : ℝ =>
      Φ (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)))
      volume (Real.pi / 3) (2 * Real.pi / 3))
    (hΨarc : ∀ q : SL(2, ℤ) ⧸ Γ, IntervalIntegrable (fun θ : ℝ =>
      Ψ (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)))
      volume (Real.pi / 3) (2 * Real.pi / 3)) :
    (∑ q : SL(2, ℤ) ⧸ Γ, ∫ y in s, Φ (Quotient.out q)⁻¹ (1 / 2 + y * Complex.I)) =
        (∑ q : SL(2, ℤ) ⧸ Γ, ∫ y in s, Φ (Quotient.out q)⁻¹ (-(1 / 2) + y * Complex.I)) +
          ∑ q : SL(2, ℤ) ⧸ Γ,
            c ((Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q) *
              ∫ y in s, Ψ (Quotient.out q)⁻¹ (-(1 / 2) + y * Complex.I) ∧
      2 * (∑ q : SL(2, ℤ) ⧸ Γ, ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
          Φ (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) *
            (Complex.I * Complex.exp (θ * Complex.I))) =
        -∑ q : SL(2, ℤ) ⧸ Γ,
          c ((Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q) *
            ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
              Ψ (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) *
                (Complex.I * Complex.exp (θ * Complex.I)) := by sorry
