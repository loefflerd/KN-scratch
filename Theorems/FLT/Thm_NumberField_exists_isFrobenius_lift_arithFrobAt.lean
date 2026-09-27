import Definitions.FLT.Def_TaylorWiles_Primes
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Normal.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NumberField Pointwise

theorem NumberField.exists_isFrobenius_lift_arithFrobAt
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField E] [IsGalois ℚ E]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)]
    [Finite (𝓞 E ⧸ Q)] :
    ∃ (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) (_ : Qt.IsMaximal)
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      Qt.LiesOver Q ∧ AlgEquiv.restrictNormal τ E = arithFrobAt ℤ (E ≃ₐ[ℚ] E) Q ∧
      (∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x ∈ Qt ↔ x ∈ Qt) ∧
      ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x - x ^ ℓ ∈ Qt := by sorry
