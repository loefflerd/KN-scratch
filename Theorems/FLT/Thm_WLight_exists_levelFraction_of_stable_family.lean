import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Geometry.Manifold.Notation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm
theorem WLight.exists_levelFraction_of_stable_family
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
    (S : Set (ℍ → ℂ))
    (hhol : ∀ G ∈ S, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hpb : ∀ G ∈ S, ∃ m : ℕ, IsBoundedAtImInfty (G * ModularForm.discriminant ^ m))
    (hst : ∀ (γ : SL(2, ℤ)), ∀ G ∈ S, (G ∘ (γ • ·)) ∈ S)
    (hinv : ∀ G ∈ S, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (γ • τ) = G τ)
    {F : ℍ → ℂ} (hF : F ∈ S) :
    ∃ a b : ℍ → ℂ,
      a ∈ Algebra.adjoin ℂ
        (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
      b ∈ Algebra.adjoin ℂ
        (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
      b ≠ 0 ∧ F * b = a := by sorry
