import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.jqN_pow_not_mem_adjoin_full (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ) (hF : jqN p ∉ modularFunctionFieldFull M) : jqN (p ^ (a + 2)) ∉ IntermediateField.adjoin ℚ ((modularFunctionFieldFull M : Set (LaurentSeries ℚ)) ∪ {x : LaurentSeries ℚ | ∃ i : ℕ, i ≤ a + 1 ∧ x = jqN (p ^ i)}) := by sorry
