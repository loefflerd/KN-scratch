import Definitions.FLT.Def_EllipticCurve_FrobeniusTrace
import Mathlib.NumberTheory.NumberField.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NumberField Pointwise

theorem ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem
    (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) [Qt.IsMaximal] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓQ : (ℓ : 𝓞 (AlgebraicClosure ℚ)) ∈ Qt) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hstab : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x ∈ Qt ↔ x ∈ Qt)
    (hfrob : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x - x ^ ℓ ∈ Qt)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ∀ x : AlgebraicClosure ℚ,
      x ∈ A ↔ ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧ ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) * x = a) :
    A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ := by sorry
