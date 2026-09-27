import Mathlib
import Definitions.FLT.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_liesOverPrime_mem_inertiaSubgroupIn (𝔔 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) [𝔔.IsMaximal] {q : ℕ} (hq : q.Prime) (hq𝔔 : (q : integralClosure ℤ (AlgebraicClosure ℚ)) ∈ 𝔔) (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ), ∃ c ∈ 𝔔, (c : AlgebraicClosure ℚ) = σ b - b) : ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q ∧ σ ∈ A.inertiaSubgroupIn ℚ := by sorry
