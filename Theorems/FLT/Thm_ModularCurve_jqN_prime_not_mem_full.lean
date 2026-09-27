import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.jqN_prime_not_mem_full (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (hpM : ¬ p ∣ M) (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d], Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d ∧ modularFunctionField d = modularFunctionFieldFull d) : jqN p ∉ modularFunctionFieldFull M := by sorry
