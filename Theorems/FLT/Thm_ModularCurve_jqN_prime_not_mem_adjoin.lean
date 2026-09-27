import Definitions.FLT.Def_ModularCurve_X0
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.jqN_prime_not_mem_adjoin (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (r : ℕ) [hr : Fact (Nat.Prime r)] (hrS : r ∉ S) : jqN r ∉ IntermediateField.adjoin ℚ (insert jq {x : LaurentSeries ℚ | ∃ p ∈ S, ∃ _ : NeZero p, x = jqN p}) := by sorry
