import Definitions.FLT.Def_ModularCurve_X0
import Mathlib.FieldTheory.Relrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.relfinrank_full_eq_mul (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ) (hup : modularFunctionFieldFull (M * p ^ (a + 1)) = IntermediateField.adjoin ℚ (insert (jqN (p ^ (a + 1))) (modularFunctionFieldFull (M * p ^ a) : Set (LaurentSeries ℚ)))) (hnm : jqN (p ^ (a + 1)) ∉ modularFunctionFieldFull (M * p ^ a)) : IntermediateField.relfinrank (modularFunctionFieldFull (M * p ^ a)) (modularFunctionFieldFull (M * p ^ (a + 1))) = if a = 0 then p + 1 else p := by sorry
