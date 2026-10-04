import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Geometry.Manifold.Notation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm
theorem WLight.levelN_structure_package
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :
    let A_N : Subalgebra ℂ (ℍ → ℂ) := Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v})
    let vecMul : (Fin 2 → ZMod N) → SL(2, ℤ) → Fin 2 → ZMod N := fun v γ ↦
      Matrix.vecMul v ((γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N))
    ({γ : SL(2, ℤ) | ∀ v : Fin 2 → ZMod N, v ≠ 0 → fricke (vecMul v γ) = fricke v} =
      {γ : SL(2, ℤ) | γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N})
    ∧ (∀ a b : ℍ → ℂ, a ∈ A_N → b ∈ A_N → b ≠ 0 →
        (∀ γ : SL(2, ℤ), a * (b ∘ (γ • ·)) = (a ∘ (γ • ·)) * b) →
        ∃ p q : Polynomial ℂ, q ≠ 0 ∧ a * (fun τ ↦ q.eval (jf τ)) = b * (fun τ ↦ p.eval (jf τ)))
    ∧ (∀ v : Fin 2 → ZMod N, v ≠ 0 → ∃ d : ℕ, ∃ c : ℕ → Polynomial ℂ,
        ∀ τ, fricke v τ ^ d
          + ∑ k ∈ Finset.range d, (c k).eval (jf τ) * fricke v τ ^ k = 0)
    ∧ (∀ P : Polynomial ℂ, (∀ τ : ℍ, P.eval (jf τ) = 0) → P = 0)
    ∧ (∀ F ∈ A_N, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    ∧ (∀ a b : ℍ → ℂ, a ∈ A_N → b ∈ A_N → a * b = 0 → a = 0 ∨ b = 0) := by sorry
