import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.finrank_adjoin_jqN_pow_succ_of_not_mem (F : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) [hp : Fact (Nat.Prime p)] (k : ℕ) (h0 : jqN (p ^ k) ∈ F) (h1 : jqN (p ^ (k + 1)) ∈ F) (hF : jqN (p ^ (k + 2)) ∉ F) : Module.finrank F (IntermediateField.adjoin F ({jqN (p ^ (k + 2))} : Set (LaurentSeries ℚ))) = p := by sorry
