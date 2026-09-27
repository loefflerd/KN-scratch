import Definitions.FLT.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.jqNModC_prime_not_mem_adjoin_of_forall_aeval_ne {K : Type*} [Field K] (p : ℕ) [hp : Fact (Nat.Prime p)] (h : ∀ P : Polynomial K, Polynomial.aeval (jqModC K) P ≠ jqNModC K p) : jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by sorry
