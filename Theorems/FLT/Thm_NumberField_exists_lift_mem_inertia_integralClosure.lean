import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem NumberField.exists_lift_mem_inertia_integralClosure (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L] (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsMaximal] {q : ℕ} (hqQ : (q : NumberField.RingOfIntegers L) ∈ Q) (τ : L ≃ₐ[ℚ] L) (hτ : τ ∈ Q.inertia (L ≃ₐ[ℚ] L)) : ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), AlgEquiv.restrictNormalHom L σ = τ ∧ ∃ 𝔔 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ)), 𝔔.IsMaximal ∧ (q : integralClosure ℤ (AlgebraicClosure ℚ)) ∈ 𝔔 ∧ ∀ b : integralClosure ℤ (AlgebraicClosure ℚ), ∃ c ∈ 𝔔, (c : AlgebraicClosure ℚ) = σ b - b := by sorry
