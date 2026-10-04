import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Adjoin.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm
theorem WLight.frickeFunction_intBaseChange
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    {G a b : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (ha : a ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb : b ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb0 : b ≠ 0) (hGb : G * b = a)
    {d : ℕ} (p : Fin d → Polynomial ℂ)
    (hprel : ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0) :
    letI kN : IntermediateField ℚ ℂ :=
      IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))}
    ∃ (n : ℕ) (lam : Fin n → ℂ) (Gi : Fin n → (ℍ → ℂ))
      (Pi Qi : Fin n → (ℍ → ℂ))
      (di : Fin n → ℕ) (pi : ∀ i, Fin (di i) → Polynomial ℂ),
      (G = ∑ i, lam i • Gi i) ∧
      (∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Gi i)) ∧
      (∀ i, Pi i ∈ Algebra.adjoin ↥kN
          (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
        Qi i ∈ Algebra.adjoin ↥kN
          (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
        Qi i ≠ 0 ∧ Gi i * Qi i = Pi i) ∧
      (∀ i k m, (pi i k).coeff m ∈ kN) ∧
      (∀ i τ, Gi i τ ^ di i +
        ∑ k : Fin (di i), (pi i k).eval (jf τ) * Gi i τ ^ (k : ℕ) = 0) := by sorry
